// This file is Copyright its original authors, visible in version control
// history.
//
// This file is licensed under the Apache License, Version 2.0 <LICENSE-APACHE
// or http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your option.
// You may not use this file except in accordance with one or both of these
// licenses.

use std::collections::{HashMap, HashSet};

use bitcoin::{TxIn, Sequence, Transaction, TxOut, OutPoint};
use bitcoin::blockdata::constants::WITNESS_SCALE_FACTOR;
use bitcoin::policy::MAX_STANDARD_TX_WEIGHT;
use crate::ln::channel::TOTAL_BITCOIN_SUPPLY_SATOSHIS;

use crate::ln::msgs;
use crate::ln::msgs::SerialId;
use crate::sign::EntropySource;

use core::ops::Deref;

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
	fn is_valid_for_initiator(&self) -> bool { self % 2 == 0 }
}

#[derive(Debug)]
pub enum AbortReason {
	CounterpartyAborted,
	UnexpectedCounterpartyMessage,
	InputsNotConfirmed,
	ReceivedTooManyTxAddInputs,
	ReceivedTooManyTxAddOutputs,
	IncorrectInputSequenceValue,
	IncorrectSerialIdParity,
	SerialIdUnknown,
	DuplicateSerialId,
	PrevTxOutInvalid,
	ExceededMaximumSatsAllowed,
	ExceededNumberOfInputsOrOutputs,
	InvalidTransactionState,
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
	require_confirmed_inputs: bool,
	holder_is_initiator: bool,
	received_tx_add_input_count: u16,
	received_tx_add_output_count: u16,
	inputs: HashMap<SerialId, TxInputWithPrevOutput>,
	prevtx_outpoints: HashSet<OutPoint>,
	outputs: HashMap<SerialId, TxOut>,
	base_tx: Transaction,
	did_send_tx_signatures: bool,
	feerate_sat_per_kw: u32,
}

impl NegotiationContext {
	fn is_valid_counterparty_serial_id(&self, serial_id: SerialId) -> bool {
		// A received `SerialId`'s parity must match the role of the counterparty.
		self.holder_is_initiator == !serial_id.is_valid_for_initiator()
	}

	fn initiator_inputs_contributed(&self) -> impl Iterator<Item = &TxInputWithPrevOutput> {
		self.inputs.iter()
			.filter(|(serial_id, _)| serial_id.is_valid_for_initiator())
			.map(|(_, input_with_prevout)| input_with_prevout)
	}

	fn non_initiator_inputs_contributed(&self) -> impl Iterator<Item = &TxInputWithPrevOutput> {
		self.inputs.iter()
			.filter(|(serial_id, _)| !serial_id.is_valid_for_initiator())
			.map(|(_, input_with_prevout)| input_with_prevout)
	}

	fn initiator_outputs_contributed(&self) -> impl Iterator<Item = &TxOut> {
		self.outputs.iter()
			.filter(|(serial_id, _)| serial_id.is_valid_for_initiator())
			.map(|(_, output)| output)
	}

	fn non_initiator_outputs_contributed(&self) -> impl Iterator<Item = &TxOut> {
		self.outputs.iter()
			.filter(|(serial_id, _)| !serial_id.is_valid_for_initiator())
			.map(|(_, output)| output)
	}

	fn receive_tx_add_input(&mut self, msg: &msgs::TxAddInput, confirmed: bool) -> Result<(), AbortReason> {
		// The interactive-txs spec calls for us to fail negotiation if the `prevtx` we receive is
		// invalid. However, we would not need to account for this explicit negotiation failure
		// mode here since `PeerManager` would already disconnect the peer if the `prevtx` is
		// invalid; implicitly ending the negotiation.

		if !self.is_valid_counterparty_serial_id(msg.serial_id) {
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

		if self.require_confirmed_inputs && !confirmed {
			return Err(AbortReason::InputsNotConfirmed);
		}

		let transaction = msg.prevtx.clone().into_transaction();

		if let Some(tx_out) = transaction.output.get(msg.prevtx_out as usize) {
			if !tx_out.script_pubkey.is_witness_program() {
				// The receiving node:
				//  - MUST fail the negotiation if:
				//     - the `scriptPubKey` is not a witness program
				return Err(AbortReason::PrevTxOutInvalid);
			} else if !self.prevtx_outpoints.insert(
				OutPoint {
					txid: transaction.txid(),
					vout: msg.prevtx_out
				}
			) {
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
		if let None = self.inputs.insert(
			msg.serial_id,
			TxInputWithPrevOutput {
				input: TxIn {
					previous_output: OutPoint { txid: transaction.txid(), vout: msg.prevtx_out },
					sequence: Sequence(msg.sequence),
					..Default::default()
				},
				prev_output: prev_out
			}
		) {
			Ok(())
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - the `serial_id` is already included in the transaction
			Err(AbortReason::DuplicateSerialId)
		}
	}

	fn receive_tx_remove_input(&mut self, serial_id: SerialId) -> Result<(), AbortReason> {
		if !self.is_valid_counterparty_serial_id(serial_id) {
			return Err(AbortReason::IncorrectSerialIdParity);
		}

		if let Some(input) = self.inputs.remove(&serial_id) {
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

	fn receive_tx_add_output(&mut self, serial_id: u64, output: TxOut) -> Result<(), AbortReason> {
		// The receiving node:
		//  - MUST fail the negotiation if:
		//     - the serial_id has the wrong parity
		if !self.is_valid_counterparty_serial_id(serial_id) {
			return Err(AbortReason::IncorrectSerialIdParity);
		}

		self.received_tx_add_output_count += 1;
		if self.received_tx_add_output_count > MAX_RECEIVED_TX_ADD_OUTPUT_COUNT {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - if has received 4096 `tx_add_output` messages during this negotiation
			return Err(AbortReason::ReceivedTooManyTxAddOutputs);
		}

		if output.value < output.script_pubkey.dust_value().to_sat() {
			// The receiving node:
			// - MUST fail the negotiation if:
			//		- the sats amount is less than the dust_limit
			return Err(AbortReason::ExceededDustLimit);
		}
		if output.value > TOTAL_BITCOIN_SUPPLY_SATOSHIS {
			// The receiving node:
			// - MUST fail the negotiation if:
			//		- the sats amount is greater than 2,100,000,000,000,000 (TOTAL_BITCOIN_SUPPLY_SATOSHIS)
			return Err(AbortReason::ExceededMaximumSatsAllowed);
		}

		// The receiving node:
		//   - MUST accept P2WSH, P2WPKH, P2TR scripts
		//   - MAY fail the negotiation if script is non-standard
		if !output.script_pubkey.is_v0_p2wpkh() && !output.script_pubkey.is_v0_p2wsh() &&
			!output.script_pubkey.is_v1_p2tr()
		{
			return Err(AbortReason::InvalidOutputScript);
		}

		if let None = self.outputs.insert(serial_id, output) {
			Ok(())
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - the `serial_id` is already included in the transaction
			Err(AbortReason::DuplicateSerialId)
		}
	}

	fn receive_tx_remove_output(&mut self, serial_id: SerialId) -> Result<(), AbortReason> {
		if !self.is_valid_counterparty_serial_id(serial_id) {
			return Err(AbortReason::IncorrectSerialIdParity);
		}
		if let Some(_) = self.outputs.remove(&serial_id) {
			Ok(())
		} else {
			Err(AbortReason::SerialIdUnknown)
		}
	}

	fn send_tx_add_input(&mut self, msg: &msgs::TxAddInput) -> Result<(), AbortReason> {
		let tx = msg.prevtx.clone().into_transaction();
		let input = TxIn {
			previous_output: OutPoint { txid: tx.txid(), vout: msg.prevtx_out },
			sequence: Sequence(msg.sequence),
			..Default::default()
		};
		let prev_output = tx.output.get(msg.prevtx_out as usize).ok_or(AbortReason::PrevTxOutInvalid)?.clone();
		self.inputs.insert(msg.serial_id, TxInputWithPrevOutput { input, prev_output });
		Ok(())
	}

	fn send_tx_add_output(&mut self, serial_id: SerialId, output: TxOut) {
		self.outputs.insert(serial_id, output);
	}

	fn send_tx_remove_input(&mut self, serial_id: SerialId) {
		self.inputs.remove(&serial_id);
	}

	fn send_tx_remove_output(&mut self, serial_id: SerialId) {
		self.outputs.remove(&serial_id);
	}

	fn build_transaction(self) -> Result<Transaction, AbortReason> {
		let tx_to_validate = Transaction {
			version: self.base_tx.version,
			lock_time: self.base_tx.lock_time,
			input: self.inputs.values().map(|p| p.input.clone()).collect(),
			output: self.outputs.values().cloned().collect(),
		};

		// The receiving node:
		// MUST fail the negotiation if:

		// - the peer's total input satoshis is less than their outputs
		let total_input_amount: u64 = self.inputs.values().map(|p| p.prev_output.value).sum();
		let total_output_amount = tx_to_validate.output.iter().map(|output| output.value).sum();
		if total_input_amount < total_output_amount {
			return Err(AbortReason::OutputsExceedInputs);
		}

		// - there are more than 252 inputs
		// - there are more than 252 outputs
		if self.inputs.len() > MAX_INPUTS_OUTPUTS_COUNT ||
			self.outputs.len() > MAX_INPUTS_OUTPUTS_COUNT {
			return Err(AbortReason::ExceededNumberOfInputsOrOutputs)
		}

		if tx_to_validate.weight() as u32 > MAX_STANDARD_TX_WEIGHT {
			return Err(AbortReason::TransactionTooLarge)
		}

		// TODO:
		// - Use existing rust-lightning/rust-bitcoin constants.
		// - How do we enforce their fees cover the witness without knowing its expected length?
		// 	 - Read eclair's code to see if they do this?
		const INPUT_WEIGHT: u64 = (32 + 4 + 4) * WITNESS_SCALE_FACTOR as u64;
		const OUTPUT_WEIGHT: u64 = 8 * WITNESS_SCALE_FACTOR as u64;

		// - the peer's paid feerate does not meet or exceed the agreed feerate (based on the minimum fee).
		if self.holder_is_initiator {
			let non_initiator_fees_contributed: u64 =
				self.non_initiator_inputs_contributed().map(|input| input.prev_output.value).sum::<u64>() -
					self.non_initiator_outputs_contributed().map(|output| output.value).sum::<u64>();
			let non_initiator_contribution_weight =
				self.non_initiator_inputs_contributed().count() as u64 * INPUT_WEIGHT +
					self.non_initiator_outputs_contributed().count() as u64 * OUTPUT_WEIGHT;
			let required_non_initiator_contribution_fee =
				self.feerate_sat_per_kw as u64 * 1000 / non_initiator_contribution_weight;
			if non_initiator_fees_contributed < required_non_initiator_contribution_fee {
				return Err(AbortReason::InsufficientFees);
			}
		} else {
			// if is the non-initiator:
			// 	- the initiator's fees do not cover the common fields (version, segwit marker + flag,
			// 		input count, output count, locktime)
			let initiator_fees_contributed: u64 =
				self.initiator_inputs_contributed().map(|input| input.prev_output.value).sum::<u64>() -
					self.initiator_outputs_contributed().map(|output| output.value).sum::<u64>();
			let initiator_contribution_weight =
				self.initiator_inputs_contributed().count() as u64 * INPUT_WEIGHT +
					self.initiator_outputs_contributed().count() as u64 * OUTPUT_WEIGHT;
			let required_initiator_contribution_fee =
				self.feerate_sat_per_kw as u64 * 1000 / initiator_contribution_weight;
			let tx_common_fields_weight =
				(4 /* version */ + 4 /* locktime */ + 1 /* input count */ + 1 /* output count */) *
					WITNESS_SCALE_FACTOR as u64 + 2 /* segwit marker + flag */;
			let tx_common_fields_fee = self.feerate_sat_per_kw as u64 * 1000 / tx_common_fields_weight;
			if initiator_fees_contributed < tx_common_fields_fee + required_initiator_contribution_fee {
				return Err(AbortReason::InsufficientFees);
			}
		}

		return Ok(tx_to_validate)
	}
}

//                   Interactive Transaction Construction negotiation
//                           from the perspective of a holder
//
//                               LocalState
//                        ┌──────────────────────────────┐
//                        │                              │
//                        │           ┌────────────────┐ │
//                        │           │(sent/received) │ │
//                        │           │tx_add_input    │ │
//                        │           │tx_add_output   │ │
//                        │           │tx_remove_input │ │
//                        │           │tx_remove_output│ │
//                        │           └───┐       ┌────┘ │
//                        │               │       ▼      │
//            ────────────┼──────────►┌───┴───────────┐  │        received_tx_complete                   ┌─────────────────────┐
//    accept_channel2     │           │               ├──┼───────────────────┐          sent_tx_complete │                     │
// or splice_ack          │     ┌─────┤  Negotiating  │  │                   ▼          ┌───────────────►│ NegotiationComplete │◄──┐
// or tx_ack_rbf          │     │     │               │  │          ┌─────────────────┐ │                │                     │   │
//    (sent or received)  │     │ ┌──►└───────────────┘  │          │                 │ │                └─────────────────────┘   │
//                              │ │                      │          │ RemoteTxComplete ├─┘                                          │
//             sent_tx_complete │ │ received_tx_add_*    │          │                 │                   ┌────────────────────┐   │
//                              │ │ received_tx_remove_* │          └─────────────────┘                   │                    │   │
//                        │     │ │                      │                                            ┌──►│ NegotiationAborted │   │
//                        │     │ └───┬───────────────┐  │        (sent/received)_tx_abort            │   │                    │   │
//                        │     │     │               │  ├────────────────────────────────────────────┘   └────────────────────┘   │
//                        │     └────►│ LocalTxComplete │  │                                                                         │
//                        │           │               ├──┼──┐                                                                      │
//                        │           └───────────────┘  │  └──────────────────────────────────────────────────────────────────────┘
//                        │                              │                         received_tx_complete
//                        │                              │
//                        └──────────────────────────────┘
//

// Channel states that can receive `(send|receive)_tx_(add|remove)_(input|output)`
trait State {}
trait LocalState {
	fn into_negotiation_context(self) -> NegotiationContext;
}
trait RemoteState: State {
	fn into_negotiation_context(self) -> NegotiationContext;
}


/// We are currently in the process of negotiating the transaction.
#[derive(Debug)]
struct LocalChange(NegotiationContext);
#[derive(Debug)]
struct RemoteChange(NegotiationContext);
/// We have sent a `tx_complete` message and are awaiting the counterparty's.
#[derive(Debug)]
struct LocalTxComplete(NegotiationContext);
/// We have received a `tx_complete` message and the counterparty is awaiting ours.
#[derive(Debug)]
struct RemoteTxComplete(NegotiationContext);
/// We have exchanged consecutive `tx_complete` messages with the counterparty and the transaction
/// negotiation is complete.
#[derive(Debug)]
struct NegotiationComplete(Transaction);
/// The negotiation has failed and cannot be continued.
#[derive(Debug)]
struct NegotiationAborted(AbortReason);

impl State for LocalChange {}
impl State for RemoteChange {}
impl State for LocalTxComplete {}
impl State for RemoteTxComplete {}
impl State for NegotiationComplete {}
impl State for NegotiationAborted {}

impl LocalState for LocalChange {
	fn into_negotiation_context(self) -> NegotiationContext { self.0 }
}
impl LocalState for LocalTxComplete {
	fn into_negotiation_context(self) -> NegotiationContext { self.0 }
}

impl RemoteState for RemoteChange {
	fn into_negotiation_context(self) -> NegotiationContext { self.0 }
}
impl RemoteState for RemoteTxComplete {
	fn into_negotiation_context(self) -> NegotiationContext { self.0 }
}

type StateTransitionResult<S> = Result<S, AbortReason>;

trait StateTransition<NewState: State, TransitionData> {
	fn transition(self, data: TransitionData) -> StateTransitionResult<NewState>;
}

macro_rules! define_state_transition {
}

// impl<S: LocalState> StateTransition<RemoteChange, (&msgs::TxAddInput, bool)> for S {
//     fn transition(self, data: (&msgs::TxAddInput, bool)) -> StateTransitionResult<RemoteChange> {
// 		let mut context = self.into_negotiation_context();
// 		context.receive_tx_add_input(data.0, data.1)?;
// 		Ok(RemoteChange(context))
//     }
// }
// impl<S: RemoteState> StateTransition<LocalChange, &msgs::TxAddInput> for S {
//     fn transition(self, data: &msgs::TxAddInput) -> StateTransitionResult<LocalChange> {
// 		let mut context = self.into_negotiation_context();
// 		context.send_tx_add_input(data)?;
// 		Ok(LocalChange(context))
//     }
// }
define_state_transitions!(
	[
		(&msgs::TxAddInput, bool),
		&msgs::TxRemoveInput,
		&msgs::TxAddOutput,
		&msgs::TxRemoveOutput,
	]
	[
		tx_add_input,
		tx_remove_input,
		tx_add_output,
		tx_remove_output,
	],
);

impl<S: LocalState> StateTransition<RemoteChange, (&msgs::TxAddInput, bool)> for S {
    fn transition(self, data: (&msgs::TxAddInput, bool)) -> StateTransitionResult<RemoteChange> {
		let mut context = self.into_negotiation_context();
		context.receive_tx_add_input(data.0, data.1)?;
		Ok(RemoteChange(context))
    }
}

impl<S: LocalState> StateTransition<RemoteChange, &msgs::TxAddOutput> for S {
    fn transition(self, data: &msgs::TxAddOutput) -> StateTransitionResult<RemoteChange> {
		let mut context = self.into_negotiation_context();
		let output = TxOut { value: data.sats, script_pubkey: data.script.clone() };
		context.receive_tx_add_output(data.serial_id, output)?;
		Ok(RemoteChange(context))
    }
}

impl<S: LocalState> StateTransition<RemoteChange, &msgs::TxRemoveInput> for S {
    fn transition(self, data: &msgs::TxRemoveInput) -> StateTransitionResult<RemoteChange> {
		let mut context = self.into_negotiation_context();
		context.receive_tx_remove_input(data.serial_id)?;
		Ok(RemoteChange(context))
    }
}

impl<S: LocalState> StateTransition<RemoteChange, &msgs::TxRemoveOutput> for S {
    fn transition(self, data: &msgs::TxRemoveOutput) -> StateTransitionResult<RemoteChange> {
		let mut context = self.into_negotiation_context();
		context.receive_tx_remove_output(data.serial_id)?;
		Ok(RemoteChange(context))
    }
}

impl<S: RemoteState> StateTransition<LocalChange, &msgs::TxAddInput> for S {
    fn transition(self, data: &msgs::TxAddInput) -> StateTransitionResult<LocalChange> {
		let mut context = self.into_negotiation_context();
		context.send_tx_add_input(data)?;
		Ok(LocalChange(context))
    }
}

impl<S: RemoteState> StateTransition<LocalChange, &msgs::TxAddOutput> for S {
    fn transition(self, data: &msgs::TxAddOutput) -> StateTransitionResult<LocalChange> {
		let mut context = self.into_negotiation_context();
		let output = TxOut { value: data.sats, script_pubkey: data.script.clone() };
		context.send_tx_add_output(data.serial_id, output);
		Ok(LocalChange(context))
    }
}

impl<S: RemoteState> StateTransition<LocalChange, &msgs::TxRemoveInput> for S {
    fn transition(self, data: &msgs::TxRemoveInput) -> StateTransitionResult<LocalChange> {
		let mut context = self.into_negotiation_context();
		context.send_tx_remove_input(data.serial_id);
		Ok(LocalChange(context))
    }
}

impl<S: RemoteState> StateTransition<LocalChange, &msgs::TxRemoveOutput> for S {
    fn transition(self, data: &msgs::TxRemoveOutput) -> StateTransitionResult<LocalChange> {
		let mut context = self.into_negotiation_context();
		context.send_tx_remove_output(data.serial_id);
		Ok(LocalChange(context))
    }
}

impl StateTransition<RemoteTxComplete, &msgs::TxComplete> for LocalChange {
    fn transition(self, _data: &msgs::TxComplete) -> StateTransitionResult<RemoteTxComplete> {
		Ok(RemoteTxComplete(self.into_negotiation_context()))
    }
}

impl StateTransition<LocalTxComplete, &msgs::TxComplete> for RemoteChange {
    fn transition(self, _data: &msgs::TxComplete) -> StateTransitionResult<LocalTxComplete> {
		Ok(LocalTxComplete(self.into_negotiation_context()))
    }
}

impl StateTransition<NegotiationComplete, &msgs::TxComplete> for LocalTxComplete {
    fn transition(self, _data: &msgs::TxComplete) -> StateTransitionResult<NegotiationComplete> {
		let context = self.into_negotiation_context();
		let tx = context.build_transaction()?;
		Ok(NegotiationComplete(tx))
    }
}

impl StateTransition<NegotiationComplete, &msgs::TxComplete> for RemoteTxComplete {
    fn transition(self, _data: &msgs::TxComplete) -> StateTransitionResult<NegotiationComplete> {
		let context = self.into_negotiation_context();
		let tx = context.build_transaction()?;
		Ok(NegotiationComplete(tx))
    }
}

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
	fn default() -> Self { Self::Indeterminate }
}

impl StateMachine {
	fn new(
		feerate_sat_per_kw: u32, require_confirmed_inputs: bool, is_initiator: bool,
		base_tx: Transaction, did_send_tx_signatures: bool,
	) -> Self {
		let context = NegotiationContext {
			 require_confirmed_inputs,
			 base_tx,
			 did_send_tx_signatures,
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
}

type StateMachineTransitionResult = Result<StateMachine, AbortReason>;

impl StateMachine {
	fn receive_tx_add_input(self, msg: &msgs::TxAddInput, confirmed: bool) -> StateMachineTransitionResult {
		let new_state = match self {
			Self::LocalChange(s) => s.transition((msg, confirmed)),
			Self::LocalTxComplete(s) => s.transition((msg, confirmed)),
			_ => Err(AbortReason::UnexpectedCounterpartyMessage),
		}?;
		Ok(StateMachine::RemoteChange(new_state))
	}

	fn receive_tx_add_output(self, msg: &msgs::TxAddOutput) -> StateMachineTransitionResult {
		let new_state = match self {
			Self::LocalChange(s) => s.transition(msg),
			Self::LocalTxComplete(s) => s.transition(msg),
			_ => Err(AbortReason::UnexpectedCounterpartyMessage),
		}?;
		Ok(StateMachine::RemoteChange(new_state))
	}

	fn receive_tx_remove_input(self, msg: &msgs::TxRemoveInput) -> StateMachineTransitionResult {
		let new_state = match self {
			Self::LocalChange(s) => s.transition(msg),
			Self::LocalTxComplete(s) => s.transition(msg),
			_ => Err(AbortReason::UnexpectedCounterpartyMessage),
		}?;
		Ok(StateMachine::RemoteChange(new_state))
	}

	fn receive_tx_remove_output(self, msg: &msgs::TxRemoveOutput) -> StateMachineTransitionResult {
		let new_state = match self {
			Self::LocalChange(s) => s.transition(msg),
			Self::LocalTxComplete(s) => s.transition(msg),
			_ => Err(AbortReason::UnexpectedCounterpartyMessage),
		}?;
		Ok(StateMachine::RemoteChange(new_state))
	}

	fn send_tx_add_input(self, msg: &msgs::TxAddInput) -> StateMachineTransitionResult {
		let new_state = match self {
			Self::RemoteChange(s) => s.transition(msg),
			Self::RemoteTxComplete(s) => s.transition(msg),
			_ => Err(AbortReason::UnexpectedCounterpartyMessage), // TODO
		}?;
		Ok(StateMachine::LocalChange(new_state))
	}

	fn send_tx_add_output(self, msg: &msgs::TxAddOutput) -> StateMachineTransitionResult {
		let new_state = match self {
			Self::RemoteChange(s) => s.transition(msg),
			Self::RemoteTxComplete(s) => s.transition(msg),
			_ => Err(AbortReason::UnexpectedCounterpartyMessage), // TODO
		}?;
		Ok(StateMachine::LocalChange(new_state))
	}

	fn send_tx_remove_input(self, msg: &msgs::TxRemoveInput) -> StateMachineTransitionResult {
		let new_state = match self {
			Self::RemoteChange(s) => s.transition(msg),
			Self::RemoteTxComplete(s) => s.transition(msg),
			_ => Err(AbortReason::UnexpectedCounterpartyMessage), // TODO
		}?;
		Ok(StateMachine::LocalChange(new_state))
	}

	fn send_tx_remove_output(self, msg: &msgs::TxRemoveOutput) -> StateMachineTransitionResult {
		let new_state = match self {
			Self::RemoteChange(s) => s.transition(msg),
			Self::RemoteTxComplete(s) => s.transition(msg),
			_ => Err(AbortReason::UnexpectedCounterpartyMessage), // TODO
		}?;
		Ok(StateMachine::LocalChange(new_state))
	}

	fn receive_tx_complete(self, msg: &msgs::TxComplete) -> StateMachineTransitionResult {
		let new_state = match self {
			Self::LocalChange(s) => s.transition(msg).map(|s| StateMachine::RemoteTxComplete(s)),
			Self::LocalTxComplete(s) => s.transition(msg).map(|s| StateMachine::NegotiationComplete(s)),
			_ => Err(AbortReason::UnexpectedCounterpartyMessage),
		}?;
		Ok(new_state)
	}

	fn send_tx_complete(self, msg: &msgs::TxComplete) -> StateMachineTransitionResult {
		let new_state = match self {
			Self::RemoteChange(s) => s.transition(msg).map(|s| StateMachine::LocalTxComplete(s)),
			Self::RemoteTxComplete(s) => s.transition(msg).map(|s| StateMachine::NegotiationComplete(s)),
			_ => Err(AbortReason::UnexpectedCounterpartyMessage), // TODO
		}?;
		Ok(new_state)
	}
}

pub struct InteractiveTxConstructor<ES: Deref> where ES::Target: EntropySource {
	state_machine: StateMachine,
	channel_id: [u8; 32],
	is_initiator: bool,
	entropy_source: ES,
	inputs_to_contribute: Vec<TxInputWithPrevOutput>,
	outputs_to_contribute: Vec<TxOut>,
}

pub enum InteractiveTxMessageSend {
	TxAddInput(msgs::TxAddInput),
	TxAddOutput(msgs::TxAddOutput),
	TxComplete(msgs::TxComplete),
}

// TODO: `InteractiveTxConstructor` methods should return an `Err` when the state machine itself
// errors out. There are two scenarios where that may occur: (1) Invalid data; causing negotiation
// to abort (2) Illegal state transition. Check spec to see if it dictates what needs to happen
// if a node receives an unexpected message.
impl<ES: Deref> InteractiveTxConstructor<ES> where ES::Target: EntropySource {
	pub fn new(
		entropy_source: ES, channel_id: [u8; 32], feerate_sat_per_kw: u32, require_confirmed_inputs: bool,
		is_initiator: bool, base_tx: Transaction, did_send_tx_signatures: bool,
		inputs_to_contribute: Vec<TxInputWithPrevOutput>, outputs_to_contribute: Vec<TxOut>,
	) -> (Self, Option<InteractiveTxMessageSend>) {
		let state_machine = StateMachine::new(
			feerate_sat_per_kw, require_confirmed_inputs, is_initiator, base_tx,
			did_send_tx_signatures
		);
		let mut constructor = Self {
			state_machine,
			channel_id,
			is_initiator,
			entropy_source,
			inputs_to_contribute,
			outputs_to_contribute,
		};
		let message_send = if is_initiator {
			Some(constructor.generate_message_send().unwrap()) // TODO
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

	// TODO: This also transitions the state machine, come up with a better name.
	fn generate_message_send(&mut self) -> Result<InteractiveTxMessageSend, ()> {
		if let Some(input_with_prevout) = self.inputs_to_contribute.pop() {
			let state_machine = core::mem::take(&mut self.state_machine);
			let msg = msgs::TxAddInput {
				channel_id: self.channel_id,
				serial_id: self.generate_local_serial_id(),
				// TODO: Needs real transaction and prevout
				prevtx: msgs::TransactionU16LenLimited(Transaction { version: 0, lock_time: bitcoin::PackedLockTime::ZERO, input: vec![], output: vec![]}),
				prevtx_out: 0,
				sequence: Sequence::ENABLE_RBF_NO_LOCKTIME.into(),
			};
			state_machine.send_tx_add_input(&msg)
				.map(|state_machine| {
					self.state_machine = state_machine;
					InteractiveTxMessageSend::TxAddInput(msg)
				})
				.map_err(|abort_reason| {
					self.state_machine = StateMachine::NegotiationAborted(NegotiationAborted(abort_reason));
				})
		} else if let Some(output) = self.outputs_to_contribute.pop() {
			let msg = msgs::TxAddOutput {
				channel_id: self.channel_id,
				serial_id: self.generate_local_serial_id(),
				sats: output.value,
				script: output.script_pubkey,
			};
			let state_machine = core::mem::take(&mut self.state_machine);
			state_machine.send_tx_add_output(&msg)
				.map(|state_machine| {
					self.state_machine = state_machine;
					InteractiveTxMessageSend::TxAddOutput(msg)
				})
				.map_err(|abort_reason| {
					self.state_machine = StateMachine::NegotiationAborted(NegotiationAborted(abort_reason));
				})
		} else {
			// TODO: Double check that we can transition back to Negotiating.
			let msg = msgs::TxComplete { channel_id: self.channel_id };
			let state_machine = core::mem::take(&mut self.state_machine);
			state_machine.send_tx_complete(&msg)
				.map(|state_machine| {
					self.state_machine = state_machine;
					InteractiveTxMessageSend::TxComplete(msg)
				})
				.map_err(|abort_reason| {
					self.state_machine = StateMachine::NegotiationAborted(NegotiationAborted(abort_reason));
				})
		}
	}

	pub fn receive_tx_add_input(&mut self, msg: &msgs::TxAddInput, confirmed: bool) -> Result<InteractiveTxMessageSend, ()> {
		let state_machine = core::mem::take(&mut self.state_machine);
		state_machine.receive_tx_add_input(msg, confirmed)
			.map(|state_machine| { self.state_machine = state_machine; })
			.map_err(|abort_reason| {
				self.state_machine = StateMachine::NegotiationAborted(NegotiationAborted(abort_reason));
			})?;
		self.generate_message_send()
	}

	pub fn receive_tx_remove_input(&mut self, msg: &msgs::TxRemoveInput) -> Result<InteractiveTxMessageSend, ()> {
		let state_machine = core::mem::take(&mut self.state_machine);
		state_machine.receive_tx_remove_input(msg)
			.map(|state_machine| { self.state_machine = state_machine; })
			.map_err(|abort_reason| {
				self.state_machine = StateMachine::NegotiationAborted(NegotiationAborted(abort_reason));
			})?;
		self.generate_message_send()
	}

	pub fn receive_tx_add_output(&mut self, msg: &msgs::TxAddOutput) -> Result<InteractiveTxMessageSend, ()> {
		let state_machine = core::mem::take(&mut self.state_machine);
		state_machine.receive_tx_add_output(msg)
			.map(|state_machine| { self.state_machine = state_machine; })
			.map_err(|abort_reason| {
				self.state_machine = StateMachine::NegotiationAborted(NegotiationAborted(abort_reason));
			})?;
		self.generate_message_send()
	}

	pub fn receive_tx_remove_output(&mut self, msg: &msgs::TxRemoveOutput) -> Result<InteractiveTxMessageSend, ()> {
		let state_machine = core::mem::take(&mut self.state_machine);
		state_machine.receive_tx_remove_output(msg)
			.map(|state_machine| { self.state_machine = state_machine; })
			.map_err(|abort_reason| {
				self.state_machine = StateMachine::NegotiationAborted(NegotiationAborted(abort_reason));
			})?;
		self.generate_message_send()
	}

	pub fn receive_tx_complete(&mut self, msg: &msgs::TxComplete) -> Result<Option<InteractiveTxMessageSend>, ()> {
		let state_machine = core::mem::take(&mut self.state_machine);
		state_machine.receive_tx_complete(msg)
			.map(|state_machine| {
				self.state_machine = state_machine;
				match &self.state_machine {
					StateMachine::RemoteTxComplete(c) => {
						Ok(Some(self.generate_message_send()?))
						// TODO: Expose built transaction
					}
					StateMachine::NegotiationComplete(c) => {
						// TODO: Expose built transaction
						Ok(None)
					}
					_ => {
						debug_assert!(false);
						Err(())
					}
				}
			})
			.map_err(|abort_reason| {
				self.state_machine = StateMachine::NegotiationAborted(NegotiationAborted(abort_reason));
			})?
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

