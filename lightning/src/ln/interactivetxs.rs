// This file is Copyright its original authors, visible in version control
// history.
//
// This file is licensed under the Apache License, Version 2.0 <LICENSE-APACHE
// or http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your option.
// You may not use this file except in accordance with one or both of these
// licenses.

use std::collections::{HashMap, HashSet};

use bitcoin::blockdata::constants::WITNESS_SCALE_FACTOR;
use bitcoin::policy::MAX_STANDARD_TX_WEIGHT;
use bitcoin::{OutPoint, Sequence, Transaction, TxIn, TxOut, PackedLockTime};

use crate::ln::channel::TOTAL_BITCOIN_SUPPLY_SATOSHIS;
use crate::ln::msgs;
use crate::ln::msgs::SerialId;
use crate::sign::EntropySource;

use core::ops::Deref;
use std::io::sink;
use bitcoin::consensus::Encodable;
use crate::util::ser::TransactionU16LenLimited;

/// The number of received `tx_add_input` messages during a negotiation at which point the
/// negotiation MUST be failed.
const MAX_RECEIVED_TX_ADD_INPUT_COUNT: u16 = 4096;

/// The number of received `tx_add_output` messages during a negotiation at which point the
/// negotiation MUST be failed.
const MAX_RECEIVED_TX_ADD_OUTPUT_COUNT: u16 = 4096;

/// The number of inputs or outputs that the state machine can have, before it MUST fail the
/// negotiation.
const MAX_INPUTS_OUTPUTS_COUNT: usize = 252;

trait SerialIdExt {
	fn is_valid_for_initiator(&self) -> bool;
}

impl SerialIdExt for SerialId {
	fn is_valid_for_initiator(&self) -> bool {
		self % 2 == 0
	}
}

#[derive(Debug)]
pub enum AbortReason {
	UnexpectedCounterpartyMessage,
	ReceivedTooManyTxAddInputs,
	ReceivedTooManyTxAddOutputs,
	IncorrectInputSequenceValue,
	IncorrectSerialIdParity,
	SerialIdUnknown,
	DuplicateSerialId,
	PrevTxOutInvalid,
	ExceededMaximumSatsAllowed,
	ExceededNumberOfInputsOrOutputs,
	TransactionTooLarge,
	ExceededDustLimit,
	InvalidOutputScript,
	InsufficientFees,
	OutputsExceedInputs,
}

#[derive(Debug)]
pub struct TxInputWithPrevOutput {
	input: TxIn,
	prev_output: TxOut,
}

#[derive(Debug)]
struct NegotiationContext {
	holder_is_initiator: bool,
	received_tx_add_input_count: u16,
	received_tx_add_output_count: u16,
	inputs: HashMap<SerialId, TxInputWithPrevOutput>,
	prevtx_outpoints: HashSet<OutPoint>,
	outputs: HashMap<SerialId, TxOut>,
	tx_locktime: PackedLockTime,
	feerate_sat_per_kw: u32,
}

impl NegotiationContext {
	fn is_serial_id_valid_for_counterparty(&self, serial_id: &SerialId) -> bool {
		// A received `SerialId`'s parity must match the role of the counterparty.
		self.holder_is_initiator == !serial_id.is_valid_for_initiator()
	}

	fn counterparty_inputs_contributed(&self) -> impl Iterator<Item=&TxInputWithPrevOutput> + Clone {
		self.inputs.iter()
			.filter(move |(serial_id, _)| self.is_serial_id_valid_for_counterparty(serial_id))
			.map(|(_, input_with_prevout)| input_with_prevout)
	}

	fn counterparty_outputs_contributed(&self) -> impl Iterator<Item=&TxOut> + Clone{
		self.outputs.iter()
			.filter(move |(serial_id, _)| self.is_serial_id_valid_for_counterparty(serial_id))
			.map(|(_, input_with_prevout)| input_with_prevout)
	}

	fn remote_tx_add_input(&mut self, msg: &msgs::TxAddInput) -> Result<(), AbortReason> {
		// The interactive-txs spec calls for us to fail negotiation if the `prevtx` we receive is
		// invalid. However, we would not need to account for this explicit negotiation failure
		// mode here since `PeerManager` would already disconnect the peer if the `prevtx` is
		// invalid; implicitly ending the negotiation.

		if !self.is_serial_id_valid_for_counterparty(&msg.serial_id) {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - the `serial_id` has the wrong parity
			return Err(AbortReason::IncorrectSerialIdParity);
		}

		if msg.sequence >= 0xFFFFFFFE {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - `sequence` is set to `0xFFFFFFFE` or `0xFFFFFFFF`
			return Err(AbortReason::IncorrectInputSequenceValue);
		}

		let transaction = msg.prevtx.clone().into_transaction();

		if let Some(tx_out) = transaction.output.get(msg.prevtx_out as usize) {
			if !tx_out.script_pubkey.is_witness_program() {
				// The receiving node:
				//  - MUST fail the negotiation if:
				//     - the `scriptPubKey` is not a witness program
				return Err(AbortReason::PrevTxOutInvalid);
			} else if !self.prevtx_outpoints.insert(OutPoint {
				txid: transaction.txid(),
				vout: msg.prevtx_out,
			}) {
				// The receiving node:
				//  - MUST fail the negotiation if:
				//     - the `prevtx` and `prevtx_vout` are identical to a previously added
				//       (and not removed) input's
				return Err(AbortReason::PrevTxOutInvalid);
			}
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - `prevtx_vout` is greater or equal to the number of outputs on `prevtx`
			return Err(AbortReason::PrevTxOutInvalid);
		}

		self.received_tx_add_input_count += 1;
		if self.received_tx_add_input_count > MAX_RECEIVED_TX_ADD_INPUT_COUNT {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - if has received 4096 `tx_add_input` messages during this negotiation
			return Err(AbortReason::ReceivedTooManyTxAddInputs);
		}

		let prev_out = if let Some(prev_out) = msg.prevtx.0.output.get(msg.prevtx_out as usize) {
			prev_out.clone()
		} else {
			return Err(AbortReason::PrevTxOutInvalid);
		};
		if let None = self.inputs.insert(msg.serial_id, TxInputWithPrevOutput {
			input: TxIn {
				previous_output: OutPoint {
					txid: transaction.txid(),
					vout: msg.prevtx_out,
				},
				sequence: Sequence(msg.sequence),
				..Default::default()
			},
			prev_output: prev_out,
		}) {
			Ok(())
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - the `serial_id` is already included in the transaction
			Err(AbortReason::DuplicateSerialId)
		}
	}

	fn remote_tx_remove_input(&mut self, msg: &msgs::TxRemoveInput) -> Result<(), AbortReason> {
		if !self.is_serial_id_valid_for_counterparty(&msg.serial_id) {
			return Err(AbortReason::IncorrectSerialIdParity);
		}

		if let Some(input) = self.inputs.remove(&msg.serial_id) {
			self.prevtx_outpoints.remove(&input.input.previous_output);
			Ok(())
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - the input or output identified by the `serial_id` was not added by the sender
			//    - the `serial_id` does not correspond to a currently added input
			Err(AbortReason::SerialIdUnknown)
		}
	}

	fn remote_tx_add_output(&mut self, msg: &msgs::TxAddOutput) -> Result<(), AbortReason> {
		// The receiving node:
		//  - MUST fail the negotiation if:
		//     - the serial_id has the wrong parity
		if !self.is_serial_id_valid_for_counterparty(&msg.serial_id) {
			return Err(AbortReason::IncorrectSerialIdParity);
		}

		self.received_tx_add_output_count += 1;
		if self.received_tx_add_output_count > MAX_RECEIVED_TX_ADD_OUTPUT_COUNT {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - if has received 4096 `tx_add_output` messages during this negotiation
			return Err(AbortReason::ReceivedTooManyTxAddOutputs);
		}

		if msg.sats < msg.script.dust_value().to_sat() {
			// The receiving node:
			// - MUST fail the negotiation if:
			//		- the sats amount is less than the dust_limit
			return Err(AbortReason::ExceededDustLimit);
		}
		if msg.sats > TOTAL_BITCOIN_SUPPLY_SATOSHIS {
			// The receiving node:
			// - MUST fail the negotiation if:
			//		- the sats amount is greater than 2,100,000,000,000,000 (TOTAL_BITCOIN_SUPPLY_SATOSHIS)
			return Err(AbortReason::ExceededMaximumSatsAllowed);
		}

		// The receiving node:
		//   - MUST accept P2WSH, P2WPKH, P2TR scripts
		//   - MAY fail the negotiation if script is non-standard
		if !msg.script.is_v0_p2wpkh() && !msg.script.is_v0_p2wsh() && !msg.script.is_v1_p2tr() {
			return Err(AbortReason::InvalidOutputScript);
		}

		let output = TxOut {
			value: msg.sats,
			script_pubkey: msg.script.clone(),
		};
		if let None = self.outputs.insert(msg.serial_id, output) {
			Ok(())
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - the `serial_id` is already included in the transaction
			Err(AbortReason::DuplicateSerialId)
		}
	}

	fn remote_tx_remove_output(&mut self, msg: &msgs::TxRemoveOutput) -> Result<(), AbortReason> {
		if !self.is_serial_id_valid_for_counterparty(&msg.serial_id) {
			return Err(AbortReason::IncorrectSerialIdParity);
		}
		if let Some(_) = self.outputs.remove(&msg.serial_id) {
			Ok(())
		} else {
			Err(AbortReason::SerialIdUnknown)
		}
	}

	fn local_tx_add_input(&mut self, msg: &msgs::TxAddInput) {
		let tx = msg.prevtx.clone().into_transaction();
		let input = TxIn {
			previous_output: OutPoint {
				txid: tx.txid(),
				vout: msg.prevtx_out,
			},
			sequence: Sequence(msg.sequence),
			..Default::default()
		};
		debug_assert!((msg.prevtx_out as usize) < tx.output.len());
		let prev_output = &tx.output[msg.prevtx_out as usize];
		self.inputs.insert(msg.serial_id, TxInputWithPrevOutput {
			input,
			prev_output: prev_output.clone(),
		});
	}

	fn local_tx_add_output(&mut self, msg: &msgs::TxAddOutput) {
		self.outputs.insert(msg.serial_id, TxOut {
			value: msg.sats,
			script_pubkey: msg.script.clone(),
		});
	}

	fn local_tx_remove_input(&mut self, msg: &msgs::TxRemoveInput) {
		self.inputs.remove(&msg.serial_id);
	}

	fn local_tx_remove_output(&mut self, msg: &msgs::TxRemoveOutput) {
		self.outputs.remove(&msg.serial_id);
	}

	fn build_transaction(self) -> Result<Transaction, AbortReason> {
		// The receiving node:
		// MUST fail the negotiation if:

		// - the peer's total input satoshis is less than their outputs
		let counterparty_inputs_contributed = self.counterparty_inputs_contributed();
		let counterparty_inputs_value: u64 = counterparty_inputs_contributed.clone()
			.map(|input| input.prev_output.value).sum();
		let counterparty_outputs_contributed = self.counterparty_outputs_contributed();
		let counterparty_outputs_value: u64 = counterparty_outputs_contributed.clone()
			.map(|output| output.value).sum();
		if counterparty_inputs_value < counterparty_outputs_value {
			return Err(AbortReason::OutputsExceedInputs);
		}

		// - there are more than 252 inputs
		// - there are more than 252 outputs
		if self.inputs.len() > MAX_INPUTS_OUTPUTS_COUNT || self.outputs.len() > MAX_INPUTS_OUTPUTS_COUNT {
			return Err(AbortReason::ExceededNumberOfInputsOrOutputs);
		}

		let tx_to_validate = Transaction {
			version: 2,
			lock_time: self.tx_locktime,
			input: self.inputs.values().map(|p| p.input.clone()).collect(),
			output: self.outputs.values().cloned().collect(),
		};
		if tx_to_validate.weight() as u32 > MAX_STANDARD_TX_WEIGHT {
			return Err(AbortReason::TransactionTooLarge);
		}

		// TODO:
		// - Use existing rust-lightning/rust-bitcoin constants.
		// - How do we enforce their fees cover the witness without knowing its expected length?
		// 	 - Read eclair's code to see if they do this?
		const INPUT_WEIGHT: u64 = (32 + 4 + 4) * WITNESS_SCALE_FACTOR as u64;

		// - the peer's paid feerate does not meet or exceed the agreed feerate (based on the minimum fee).
		let counterparty_output_weight_contributed: u64 = counterparty_outputs_contributed.clone().map(|output|
			(8 /* value */ + output.script_pubkey.consensus_encode(&mut sink()).unwrap() as u64) *
				WITNESS_SCALE_FACTOR as u64
		).sum();
		let counterparty_weight_contributed = counterparty_output_weight_contributed +
			counterparty_outputs_contributed.clone().count() as u64 * INPUT_WEIGHT;
		let counterparty_fees_contributed =
			counterparty_inputs_value.saturating_sub(counterparty_outputs_value);
		let mut required_counterparty_contribution_fee =
			self.feerate_sat_per_kw as u64 * 1000 / counterparty_weight_contributed;
		if !self.holder_is_initiator {
		    // if is the non-initiator:
		    // 	- the initiator's fees do not cover the common fields (version, segwit marker + flag,
		    // 		input count, output count, locktime)
		    let tx_common_fields_weight =
		        (4 /* version */ + 4 /* locktime */ + 1 /* input count */ + 1 /* output count */) *
		            WITNESS_SCALE_FACTOR as u64 + 2 /* segwit marker + flag */;
		    let tx_common_fields_fee = self.feerate_sat_per_kw as u64 * 1000 / tx_common_fields_weight;
		    required_counterparty_contribution_fee += tx_common_fields_fee;
		}
		if counterparty_fees_contributed < required_counterparty_contribution_fee {
		    return Err(AbortReason::InsufficientFees);
		}

		Ok(tx_to_validate)
	}
}

// Channel states that can receive `(send|receive)_tx_(add|remove)_(input|output)`
trait State {}

trait LocalState: State {
	fn into_negotiation_context(self) -> NegotiationContext;
}

trait RemoteState: State {
	fn into_negotiation_context(self) -> NegotiationContext;
}

macro_rules! define_state {
	(LOCAL_STATE, $state: ident, $doc: expr) => {
		define_state!($state, NegotiationContext, $doc);
		impl LocalState for $state {
			fn into_negotiation_context(self) -> NegotiationContext {
				self.0
			}
		}
	};
	(REMOTE_STATE, $state: ident, $doc: expr) => {
		define_state!($state, NegotiationContext, $doc);
		impl RemoteState for $state {
			fn into_negotiation_context(self) -> NegotiationContext {
				self.0
			}
		}
	};
	($state: ident, $inner: ident, $doc: expr) => {
		#[doc = $doc]
		#[derive(Debug)]
		struct $state($inner);
		impl State for $state {}
	};
}

define_state!(LOCAL_STATE, LocalChange, "We have sent a message to the counterparty that has affected our negotiation state.");
define_state!(LOCAL_STATE, LocalTxComplete, "We have sent a `tx_complete` message and are awaiting the counterparty's.");
define_state!(REMOTE_STATE, RemoteChange, "We have received a message from the counterparty that has affected our negotiation state.");
define_state!(REMOTE_STATE, RemoteTxComplete, "We have received a `tx_complete` message and the counterparty is awaiting ours.");
define_state!(NegotiationComplete, Transaction, "We have exchanged consecutive `tx_complete` messages with the counterparty and the transaction negotiation is complete.");
define_state!(NegotiationAborted, AbortReason, "The negotiation has failed and cannot be continued.");

type StateTransitionResult<S> = Result<S, AbortReason>;

trait StateTransition<NewState: State, TransitionData> {
	fn transition(self, data: TransitionData) -> StateTransitionResult<NewState>;
}

macro_rules! define_state_transitions {
	(LOCAL_STATE, [$(DATA $data: ty, TRANSITION $transition: ident),+]) => {
		$(
			impl<S: LocalState> StateTransition<RemoteChange, $data> for S {
				fn transition(self, data: $data) -> StateTransitionResult<RemoteChange> {
					let mut context = self.into_negotiation_context();
					let _ = context.$transition(data)?;
					Ok(RemoteChange(context))
				}
			}
		 )*
	};
	(REMOTE_STATE, [$(DATA $data: ty, TRANSITION $transition: ident),+]) => {
		$(
			impl<S: RemoteState> StateTransition<LocalChange, $data> for S {
				fn transition(self, data: $data) -> StateTransitionResult<LocalChange> {
					let mut context = self.into_negotiation_context();
					let _ = context.$transition(data);
					Ok(LocalChange(context))
				}
			}
		 )*
	};
	(TX_COMPLETE_AS_ACK, $from_state: ident, $to_state: ident) => {
		impl StateTransition<$to_state, &msgs::TxComplete> for $from_state {
			fn transition(self, _data: &msgs::TxComplete) -> StateTransitionResult<$to_state> {
				Ok($to_state(self.into_negotiation_context()))
			}
		}
	};
	(TX_COMPLETE, $from_state: ident) => {
		impl StateTransition<NegotiationComplete, &msgs::TxComplete> for $from_state {
			fn transition(self, _data: &msgs::TxComplete) -> StateTransitionResult<NegotiationComplete> {
				let context = self.into_negotiation_context();
				let tx = context.build_transaction()?;
				Ok(NegotiationComplete(tx))
			}
		}
	};
}

define_state_transitions!(LOCAL_STATE, [
	DATA &msgs::TxAddInput, TRANSITION remote_tx_add_input,
	DATA &msgs::TxRemoveInput, TRANSITION remote_tx_remove_input,
	DATA &msgs::TxAddOutput, TRANSITION remote_tx_add_output,
	DATA &msgs::TxRemoveOutput, TRANSITION remote_tx_remove_output
]);
define_state_transitions!(REMOTE_STATE, [
	DATA &msgs::TxAddInput, TRANSITION local_tx_add_input,
	DATA &msgs::TxRemoveInput, TRANSITION local_tx_remove_input,
	DATA &msgs::TxAddOutput, TRANSITION local_tx_add_output,
	DATA &msgs::TxRemoveOutput, TRANSITION local_tx_remove_output
]);
define_state_transitions!(TX_COMPLETE_AS_ACK, LocalChange, RemoteTxComplete);
define_state_transitions!(TX_COMPLETE_AS_ACK, RemoteChange, LocalTxComplete);
define_state_transitions!(TX_COMPLETE, LocalTxComplete);
define_state_transitions!(TX_COMPLETE, RemoteTxComplete);

#[derive(Debug)]
enum StateMachine {
	Indeterminate,
	LocalChange(LocalChange),
	RemoteChange(RemoteChange),
	LocalTxComplete(LocalTxComplete),
	RemoteTxComplete(RemoteTxComplete),
	NegotiationComplete(NegotiationComplete),
	NegotiationAborted(NegotiationAborted),
}

impl Default for StateMachine {
	fn default() -> Self {
		Self::Indeterminate
	}
}

macro_rules! define_state_machine_transitions {
	($transition: ident, $msg: ty, [$(FROM $from_state: ident, TO $to_state: ident),+]) => {
		fn $transition(self, msg: $msg) -> StateMachine {
			match self {
				$(
					Self::$from_state(s) => match s.transition(msg) {
						Ok(new_state) => StateMachine::$to_state(new_state),
						Err(abort_reason) => StateMachine::NegotiationAborted(NegotiationAborted(abort_reason)),
					}
				 )*
				_ => StateMachine::NegotiationAborted(NegotiationAborted(AbortReason::UnexpectedCounterpartyMessage)),
			}
		}
	};
	(LOCAL_OR_REMOTE_CHANGE, $to_local_transition: ident, $to_remote_transition: ident, $msg: ty) => {
		define_state_machine_transitions!($to_local_transition, $msg, [
			FROM RemoteChange, TO LocalChange,
			FROM RemoteTxComplete, TO LocalChange
		]);
		define_state_machine_transitions!($to_remote_transition, $msg, [
			FROM LocalChange, TO RemoteChange,
			FROM LocalTxComplete, TO RemoteChange
		]);
	};
}

impl StateMachine {
	fn new(feerate_sat_per_kw: u32, is_initiator: bool, tx_locktime: PackedLockTime) -> Self {
		let context = NegotiationContext {
			tx_locktime,
			holder_is_initiator: is_initiator,
			received_tx_add_input_count: 0,
			received_tx_add_output_count: 0,
			inputs: HashMap::new(),
			prevtx_outpoints: HashSet::new(),
			outputs: HashMap::new(),
			feerate_sat_per_kw,
		};
		if is_initiator {
			Self::RemoteChange(RemoteChange(context))
		} else {
			Self::LocalChange(LocalChange(context))
		}
	}

	define_state_machine_transitions!(
		LOCAL_OR_REMOTE_CHANGE, local_tx_add_input, remote_tx_add_input, &msgs::TxAddInput
	);
	define_state_machine_transitions!(
		LOCAL_OR_REMOTE_CHANGE, local_tx_add_output, remote_tx_add_output, &msgs::TxAddOutput
	);
	define_state_machine_transitions!(
		LOCAL_OR_REMOTE_CHANGE, local_tx_remove_input, remote_tx_remove_input, &msgs::TxRemoveInput
	);
	define_state_machine_transitions!(
		LOCAL_OR_REMOTE_CHANGE, local_tx_remove_output, remote_tx_remove_output, &msgs::TxRemoveOutput
	);
	define_state_machine_transitions!(local_tx_complete, &msgs::TxComplete, [
		FROM RemoteChange, TO LocalTxComplete,
		FROM RemoteTxComplete, TO NegotiationComplete
	]);
	define_state_machine_transitions!(remote_tx_complete, &msgs::TxComplete, [
		FROM LocalChange, TO RemoteTxComplete,
		FROM LocalTxComplete, TO NegotiationComplete
	]);
}

pub struct InteractiveTxConstructor<ES: Deref>
	where
		ES::Target: EntropySource,
{
	state_machine: StateMachine,
	channel_id: [u8; 32],
	is_initiator: bool,
	entropy_source: ES,
	inputs_to_contribute: Vec<(TxIn, Transaction)>,
	outputs_to_contribute: Vec<TxOut>,
}

pub enum InteractiveTxMessageSend {
	TxAddInput(msgs::TxAddInput),
	TxAddOutput(msgs::TxAddOutput),
	TxComplete(msgs::TxComplete),
}

macro_rules! do_state_transition {
	($self: ident, $transition: ident, $msg: expr) => {{
		let state_machine = core::mem::take(&mut $self.state_machine);
		$self.state_machine = state_machine.$transition($msg);
		match &$self.state_machine {
			StateMachine::NegotiationAborted(_) => Err(()),
			_ => Ok(()),
		}
	}};
}

// TODO: Check spec to see if it dictates what needs to happen if a node receives an unexpected message.
impl<ES: Deref> InteractiveTxConstructor<ES>
	where
		ES::Target: EntropySource,
{
	pub fn new(
		entropy_source: ES, channel_id: [u8; 32], feerate_sat_per_kw: u32, is_initiator: bool,
		tx_locktime: PackedLockTime, inputs_to_contribute: Vec<(TxIn, Transaction)>,
		outputs_to_contribute: Vec<TxOut>,
	) -> (Self, Option<InteractiveTxMessageSend>) {
		let state_machine = StateMachine::new(feerate_sat_per_kw, is_initiator, tx_locktime);
		let mut constructor = Self {
			state_machine,
			channel_id,
			is_initiator,
			entropy_source,
			inputs_to_contribute,
			outputs_to_contribute,
		};
		let message_send = if is_initiator {
			match constructor.do_local_state_transition() {
				Ok(msg_send) => Some(msg_send),
				Err(_) => {
					debug_assert!(false, "We should always be able to start our state machine successfully");
					None
				}
			}
		} else {
			None
		};
		(constructor, message_send)
	}

	fn generate_local_serial_id(&self) -> SerialId {
		let rand_bytes = self.entropy_source.get_secure_random_bytes();
		let mut serial_id_bytes = [0u8; 8];
		serial_id_bytes.copy_from_slice(&rand_bytes[..8]);
		let mut serial_id = u64::from_be_bytes(serial_id_bytes);
		if serial_id.is_valid_for_initiator() != self.is_initiator {
			serial_id ^= 1;
		}
		serial_id
	}

	fn do_local_state_transition(&mut self) -> Result<InteractiveTxMessageSend, ()> {
		if let Some((input, prev_tx)) = self.inputs_to_contribute.pop() {
			let msg = msgs::TxAddInput {
				channel_id: self.channel_id,
				serial_id: self.generate_local_serial_id(),
				prevtx: TransactionU16LenLimited(prev_tx),
				prevtx_out: input.previous_output.vout,
				sequence: input.sequence.to_consensus_u32(),
			};
			let _ = do_state_transition!(self, local_tx_add_input, &msg)?;
			Ok(InteractiveTxMessageSend::TxAddInput(msg))
		} else if let Some(output) = self.outputs_to_contribute.pop() {
			let msg = msgs::TxAddOutput {
				channel_id: self.channel_id,
				serial_id: self.generate_local_serial_id(),
				sats: output.value,
				script: output.script_pubkey,
			};
			let _ = do_state_transition!(self, local_tx_add_output, &msg)?;
			Ok(InteractiveTxMessageSend::TxAddOutput(msg))
		} else {
			let msg = msgs::TxComplete { channel_id: self.channel_id };
			let _ = do_state_transition!(self, local_tx_complete, &msg)?;
			Ok(InteractiveTxMessageSend::TxComplete(msg))
		}
	}

	pub fn handle_tx_add_input(&mut self, msg: &msgs::TxAddInput) -> Result<InteractiveTxMessageSend, ()> {
		let _ = do_state_transition!(self, remote_tx_add_input, msg)?;
		self.do_local_state_transition()
	}

	pub fn handle_tx_remove_input(&mut self, msg: &msgs::TxRemoveInput) -> Result<InteractiveTxMessageSend, ()> {
		let _ = do_state_transition!(self, remote_tx_remove_input, msg)?;
		self.do_local_state_transition()
	}

	pub fn handle_tx_add_output(&mut self, msg: &msgs::TxAddOutput) -> Result<InteractiveTxMessageSend, ()> {
		let _ = do_state_transition!(self, remote_tx_add_output, msg)?;
		self.do_local_state_transition()
	}

	pub fn handle_tx_remove_output(&mut self, msg: &msgs::TxRemoveOutput) -> Result<InteractiveTxMessageSend, ()> {
		let _ = do_state_transition!(self, remote_tx_remove_output, msg)?;
		self.do_local_state_transition()
	}

	pub fn handle_tx_complete(&mut self, msg: &msgs::TxComplete) -> Result<(Option<InteractiveTxMessageSend>, Option<Transaction>), ()> {
		let _ = do_state_transition!(self, remote_tx_complete, msg)?;
		match &self.state_machine {
			StateMachine::RemoteTxComplete(_) => {
				let msg_send = self.do_local_state_transition()?;
				let negotiated_tx = match &self.state_machine {
					StateMachine::NegotiationComplete(s) => Some(s.0.clone()),
					StateMachine::LocalChange(_) => None, // We either had an input or output to contribute.
					_ => {
						debug_assert!(false, "We cannot transition to any other states after receiving `tx_complete` and responding");
						return Err(());
					}
				};
				Ok((Some(msg_send), negotiated_tx))
			}
			StateMachine::NegotiationComplete(s) => Ok((None, Some(s.0.clone()))),
			_ => {
				debug_assert!(false, "We cannot transition to any other states after receiving `tx_complete`");
				Err(())
			}
		}
	}
}

// #[cfg(test)]
// mod tests {
// 	use core::str::FromStr;
// 	use crate::chain::chaininterface::FEERATE_FLOOR_SATS_PER_KW;
// use crate::ln::interactivetxs::ChannelMode::{Negotiating, NegotiationAborted};
// 	use crate::ln::interactivetxs::{AbortReason, ChannelMode, InteractiveTxConstructor, InteractiveTxStateMachine};
// 	use crate::ln::msgs::TransactionU16LenLimited;
// 	use bitcoin::consensus::encode;
// 	use bitcoin::{Address, PackedLockTime, Script, Sequence, Transaction, Txid, TxIn, TxOut, Witness};
// 	use bitcoin::hashes::hex::FromHex;
// 	use crate::chain::transaction::OutPoint;
// 	use crate::ln::interactivetxs::AbortReason::IncorrectSerialIdParity;
// 	use crate::ln::msgs::TxAddInput;
//
// 	#[test]
// 	fn test_invalid_counterparty_serial_id_should_abort_negotiation() {
// 		let tx: Transaction = encode::deserialize(&hex::decode("020000000001010e0ade\
// 			f48412e4361325ac1c6e36411299ab09d4f083b9d8ddb55fbc06e1b0c00000000000feffffff0220a107000\
// 			0000000220020f81d95e040bd0a493e38bae27bff52fe2bb58b93b293eb579c01c31b05c5af1dc072cfee54\
// 			a3000016001434b1d6211af5551905dc2642d05f5b04d25a8fe80247304402207f570e3f0de50546aad25a8\
// 			72e3df059d277e776dda4269fa0d2cc8c2ee6ec9a022054e7fae5ca94d47534c86705857c24ceea3ad51c69\
// 			dd6051c5850304880fc43a012103cb11a1bacc223d98d91f1946c6752e358a5eb1a1c983b3e6fb15378f453\
// 			b76bd00000000").unwrap()[..]).unwrap();
// 		let mut constructor = InteractiveTxConstructor::new([0; 32], FEERATE_FLOOR_SATS_PER_KW, true, true, tx, false);
// 		constructor.receive_tx_add_input(2, &get_sample_tx_add_input(), false);
// 		assert!(matches!(constructor.mode, ChannelMode::NegotiationAborted { .. }))
// 	}
//
// 	impl DummyChannel {
// 		fn new() -> Self {
// 			let tx: Transaction = encode::deserialize(&hex::decode("020000000001010e0ade\
// 			f48412e4361325ac1c6e36411299ab09d4f083b9d8ddb55fbc06e1b0c00000000000feffffff0220a107000\
// 			0000000220020f81d95e040bd0a493e38bae27bff52fe2bb58b93b293eb579c01c31b05c5af1dc072cfee54\
// 			a3000016001434b1d6211af5551905dc2642d05f5b04d25a8fe80247304402207f570e3f0de50546aad25a8\
// 			72e3df059d277e776dda4269fa0d2cc8c2ee6ec9a022054e7fae5ca94d47534c86705857c24ceea3ad51c69\
// 			dd6051c5850304880fc43a012103cb11a1bacc223d98d91f1946c6752e358a5eb1a1c983b3e6fb15378f453\
// 			b76bd00000000").unwrap()[..]).unwrap();
// 			Self {
// 				tx_constructor: InteractiveTxConstructor::new([0; 32], FEERATE_FLOOR_SATS_PER_KW, true, true, tx, false)
// 			}
// 		}
//
// 		fn handle_add_tx_input(&mut self) {
// 			self.tx_constructor.receive_tx_add_input(1234, &get_sample_tx_add_input(), true)
// 		}
// 	}
//
// 	// Fixtures
// 	fn get_sample_tx_add_input() -> TxAddInput {
// 		let prevtx = TransactionU16LenLimited::new(
// 			Transaction {
// 				version: 2,
// 				lock_time: PackedLockTime(0),
// 				input: vec![TxIn {
// 					previous_output: OutPoint { txid: Txid::from_hex("305bab643ee297b8b6b76b320792c8223d55082122cb606bf89382146ced9c77").unwrap(), index: 2 }.into_bitcoin_outpoint(),
// 					script_sig: Script::new(),
// 					sequence: Sequence(0xfffffffd),
// 					witness: Witness::from_vec(vec![
// 						hex::decode("304402206af85b7dd67450ad12c979302fac49dfacbc6a8620f49c5da2b5721cf9565ca502207002b32fed9ce1bf095f57aeb10c36928ac60b12e723d97d2964a54640ceefa701").unwrap(),
// 						hex::decode("0301ab7dc16488303549bfcdd80f6ae5ee4c20bf97ab5410bbd6b1bfa85dcd6944").unwrap()]),
// 				}],
// 				output: vec![
// 					TxOut {
// 						value: 12704566,
// 						script_pubkey: Address::from_str("bc1qzlffunw52jav8vwdu5x3jfk6sr8u22rmq3xzw2").unwrap().script_pubkey(),
// 					},
// 					TxOut {
// 						value: 245148,
// 						script_pubkey: Address::from_str("bc1qxmk834g5marzm227dgqvynd23y2nvt2ztwcw2z").unwrap().script_pubkey(),
// 					},
// 				],
// 			}
// 		).unwrap();
//
// 		return TxAddInput {
// 			channel_id: [2; 32],
// 			serial_id: 4886718345,
// 			prevtx,
// 			prevtx_out: 305419896,
// 			sequence: 305419896,
// 		};
// 	}
// }
