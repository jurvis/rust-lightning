// This file is Copyright its original authors, visible in version control
// history.
//
// This file is licensed under the Apache License, Version 2.0 <LICENSE-APACHE
// or http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your option.
// You may not use this file except in accordance with one or both of these
// licenses.

use std::collections::{HashMap, HashSet};

use bitcoin::{TxIn, Sequence, Transaction, TxOut, OutPoint, Witness};
use bitcoin::blockdata::constants::WITNESS_SCALE_FACTOR;
use bitcoin::policy::MAX_STANDARD_TX_WEIGHT;
use crate::ln::channel::TOTAL_BITCOIN_SUPPLY_SATOSHIS;

use crate::ln::interactivetxs::ChannelMode::Indeterminate;
use crate::ln::msgs;
use crate::ln::msgs::SerialId;
use crate::sign::EntropySource;

use core::ops::Deref;
use std::process::abort;

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

pub(crate) enum AbortReason {
	CounterpartyAborted,
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

//                   Interactive Transaction Construction negotiation
//                           from the perspective of a holder
//
//                               AcceptingChanges
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
//                              │ │                      │          │ TheirTxComplete ├─┘                                          │
//             sent_tx_complete │ │ received_tx_add_*    │          │                 │                   ┌────────────────────┐   │
//                              │ │ received_tx_remove_* │          └─────────────────┘                   │                    │   │
//                        │     │ │                      │                                            ┌──►│ NegotiationAborted │   │
//                        │     │ └───┬───────────────┐  │        (sent/received)_tx_abort            │   │                    │   │
//                        │     │     │               │  ├────────────────────────────────────────────┘   └────────────────────┘   │
//                        │     └────►│ OurTxComplete │  │                                                                         │
//                        │           │               ├──┼──┐                                                                      │
//                        │           └───────────────┘  │  └──────────────────────────────────────────────────────────────────────┘
//                        │                              │                         received_tx_complete
//                        │                              │
//                        └──────────────────────────────┘
//

// Channel states that can receive `(send|receive)_tx_(add|remove)_(input|output)`
pub(crate) trait AcceptingChanges {
	fn into_negotiation_context(self) -> NegotiationContext;
}

/// We are currently in the process of negotiating the transaction.
pub(crate) struct Negotiating(NegotiationContext);
/// We have sent a `tx_complete` message and are awaiting the counterparty's.
pub(crate) struct OurTxComplete(NegotiationContext);
/// We have received a `tx_complete` message and the counterparty is awaiting ours.
pub(crate) struct TheirTxComplete(NegotiationContext);
/// We have exchanged consecutive `tx_complete` messages with the counterparty and the transaction
/// negotiation is complete.
pub(crate) struct NegotiationComplete(Transaction);
/// The negotiation has failed and cannot be continued.
pub(crate) struct NegotiationAborted(AbortReason);

impl AcceptingChanges for Negotiating {
	fn into_negotiation_context(self) -> NegotiationContext { self.0 }
}
impl AcceptingChanges for OurTxComplete {
	fn into_negotiation_context(self) -> NegotiationContext { self.0 }
}
impl AcceptingChanges for TheirTxComplete {
	fn into_negotiation_context(self) -> NegotiationContext { self.0 }
}

struct TxInputWithPrevOutput {
	input: TxIn,
	prev_output: TxOut,
}

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
}

struct InteractiveTxStateMachine<S>(S);

type InteractiveTxStateMachineResult<S> =
	Result<InteractiveTxStateMachine<S>, InteractiveTxStateMachine<NegotiationAborted>>;

impl InteractiveTxStateMachine<Negotiating> {
	fn new(
		feerate_sat_per_kw: u32, require_confirmed_inputs: bool, is_initiator: bool,
		base_tx: Transaction, did_send_tx_signatures: bool,
	) -> Self {
		Self(Negotiating(NegotiationContext {
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
		}))
	}
}

impl<S> InteractiveTxStateMachine<S> where S: AcceptingChanges {
	fn abort_negotiation(self, reason: AbortReason) -> InteractiveTxStateMachineResult<Negotiating> {
		Err(InteractiveTxStateMachine(NegotiationAborted(reason)))
	}

	fn receive_tx_add_input(mut self, msg: &msgs::TxAddInput, confirmed: bool) -> InteractiveTxStateMachineResult<Negotiating> {
		let mut negotiation_context = self.0.into_negotiation_context();

		// The interactive-txs spec calls for us to fail negotiation if the `prevtx` we receive is
		// invalid. However, we would not need to account for this explicit negotiation failure
		// mode here since `PeerManager` would already disconnect the peer if the `prevtx` is
		// invalid; implicitly ending the negotiation.

		if !negotiation_context.is_valid_counterparty_serial_id(msg.serial_id) {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - the `serial_id` has the wrong parity
			return self.abort_negotiation(AbortReason::IncorrectSerialIdParity);
		}

		if msg.sequence >= 0xFFFFFFFE {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - `sequence` is set to `0xFFFFFFFE` or `0xFFFFFFFF`
			return self.abort_negotiation(AbortReason::IncorrectInputSequenceValue);
		}

		if negotiation_context.require_confirmed_inputs && !confirmed {
			return self.abort_negotiation(AbortReason::InputsNotConfirmed);
		}

		let transaction = msg.prevtx.clone().into_transaction();

		if let Some(tx_out) = transaction.output.get(msg.prevtx_out as usize) {
			if !tx_out.script_pubkey.is_witness_program() {
				// The receiving node:
				//  - MUST fail the negotiation if:
				//     - the `scriptPubKey` is not a witness program
				return self.abort_negotiation(AbortReason::PrevTxOutInvalid);
			} else if !negotiation_context.prevtx_outpoints.insert(
				OutPoint {
					txid: transaction.txid(),
					vout: msg.prevtx_out
				}
			) {
				// The receiving node:
				//  - MUST fail the negotiation if:
				//     - the `prevtx` and `prevtx_vout` are identical to a previously added
				//       (and not removed) input's
				return self.abort_negotiation(AbortReason::PrevTxOutInvalid);
			}
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - `prevtx_vout` is greater or equal to the number of outputs on `prevtx`
			return self.abort_negotiation(AbortReason::PrevTxOutInvalid);
		}

		negotiation_context.received_tx_add_input_count += 1;
		if negotiation_context.received_tx_add_input_count > MAX_RECEIVED_TX_ADD_INPUT_COUNT {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - if has received 4096 `tx_add_input` messages during this negotiation
			return self.abort_negotiation(AbortReason::ReceivedTooManyTxAddInputs);
		}

		let prev_out = if let Some(prev_out) = msg.prevtx.0.output.get(msg.prevtx_out as usize) {
			prev_out.clone()
		} else {
			return self.abort_negotiation(AbortReason::PrevTxOutInvalid);
		};
		if let None = negotiation_context.inputs.insert(
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
			Ok(InteractiveTxStateMachine(Negotiating(negotiation_context)))
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - the `serial_id` is already included in the transaction
			self.abort_negotiation(AbortReason::DuplicateSerialId)
		}
	}

	fn receive_tx_remove_input(mut self, serial_id: SerialId) -> InteractiveTxStateMachineResult<Negotiating> {
		let mut negotiation_context = self.0.into_negotiation_context();
		if !negotiation_context.is_valid_counterparty_serial_id(serial_id) {
			return self.abort_negotiation(AbortReason::IncorrectSerialIdParity);
		}

		if let Some(input) = negotiation_context.inputs.remove(&serial_id) {
			negotiation_context.prevtx_outpoints.remove(&input.input.previous_output);
			Ok(InteractiveTxStateMachine(Negotiating(negotiation_context)))
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - the input or output identified by the `serial_id` was not added by the sender
			//    - the `serial_id` does not correspond to a currently added input
			self.abort_negotiation(AbortReason::SerialIdUnknown)
		}
	}

	fn receive_tx_add_output(mut self, serial_id: u64, output: TxOut) -> InteractiveTxStateMachineResult<Negotiating> {
		let mut negotiation_context = self.0.into_negotiation_context();

		// The receiving node:
		//  - MUST fail the negotiation if:
		//     - the serial_id has the wrong parity
		if !negotiation_context.is_valid_counterparty_serial_id(serial_id) {
			return self.abort_negotiation(AbortReason::IncorrectSerialIdParity);
		}

		negotiation_context.received_tx_add_output_count += 1;
		if negotiation_context.received_tx_add_output_count > MAX_RECEIVED_TX_ADD_OUTPUT_COUNT {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - if has received 4096 `tx_add_output` messages during this negotiation
			return self.abort_negotiation(AbortReason::ReceivedTooManyTxAddOutputs);
		}

		if output.value < output.script_pubkey.dust_value().to_sat() {
			// The receiving node:
			// - MUST fail the negotiation if:
			//		- the sats amount is less than the dust_limit
			return self.abort_negotiation(AbortReason::ExceededDustLimit);
		}
		if output.value > TOTAL_BITCOIN_SUPPLY_SATOSHIS {
			// The receiving node:
			// - MUST fail the negotiation if:
			//		- the sats amount is greater than 2,100,000,000,000,000 (TOTAL_BITCOIN_SUPPLY_SATOSHIS)
			return self.abort_negotiation(AbortReason::ExceededMaximumSatsAllowed);
		}

		// The receiving node:
		//   - MUST accept P2WSH, P2WPKH, P2TR scripts
		//   - MAY fail the negotiation if script is non-standard
		if !output.script_pubkey.is_v0_p2wpkh() && !output.script_pubkey.is_v0_p2wsh() &&
			!output.script_pubkey.is_v1_p2tr()
		{
			return self.abort_negotiation(AbortReason::InvalidOutputScript);
		}

		if let None = negotiation_context.outputs.insert(serial_id, output) {
			Ok(InteractiveTxStateMachine(Negotiating(negotiation_context)))
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - the `serial_id` is already included in the transaction
			self.abort_negotiation(AbortReason::DuplicateSerialId)
		}
	}

	fn receive_tx_remove_output(mut self, serial_id: SerialId) -> InteractiveTxStateMachineResult<Negotiating> {
		let mut negotiation_context = self.0.into_negotiation_context();

		if !negotiation_context.is_valid_counterparty_serial_id(serial_id) {
			return self.abort_negotiation(AbortReason::IncorrectSerialIdParity);
		}

		if let Some(output) = negotiation_context.outputs.remove(&serial_id) {
			Ok(InteractiveTxStateMachine(Negotiating(negotiation_context)))
		} else {
			self.abort_negotiation(AbortReason::SerialIdUnknown)
		}
	}

	fn send_tx_add_input(mut self, serial_id: u64, input: TxIn, prevout: TxOut) -> InteractiveTxStateMachine<Negotiating> {
		let mut negotiation_context = self.0.into_negotiation_context();
		negotiation_context.inputs.insert(
			serial_id,
			TxInputWithPrevOutput {
				input: input,
				prev_output: prevout
			}
		);
		InteractiveTxStateMachine(Negotiating(negotiation_context))
	}

	fn send_tx_add_output(mut self, serial_id: SerialId, output: TxOut) -> InteractiveTxStateMachine<Negotiating> {
		let mut negotiation_context = self.0.into_negotiation_context();
		negotiation_context.outputs.insert(serial_id, output);
		InteractiveTxStateMachine(Negotiating(negotiation_context))
	}

	fn send_tx_remove_input(mut self, serial_id: SerialId) -> InteractiveTxStateMachine<Negotiating> {
		let mut negotiation_context = self.0.into_negotiation_context();
		negotiation_context.inputs.remove(&serial_id);
		InteractiveTxStateMachine(Negotiating(negotiation_context))
	}

	fn send_tx_remove_output(mut self, serial_id: SerialId) -> InteractiveTxStateMachine<Negotiating> {
		let mut negotiation_context = self.0.into_negotiation_context();
		negotiation_context.outputs.remove(&serial_id);
		InteractiveTxStateMachine(Negotiating(negotiation_context))
	}

	fn send_tx_abort(mut self) -> InteractiveTxStateMachine<NegotiationAborted> {
		// A sending node:
		// 	- MUST NOT have already transmitted tx_signatures
		// 	- SHOULD forget the current negotiation and reset their state.
		todo!();
	}

	fn receive_tx_abort(mut self) -> InteractiveTxStateMachine<NegotiationAborted> {
		todo!();
	}

	// TODO: This should only be on Our/TheirTxComplete?
	fn build_transaction(mut self) -> Result<Transaction, AbortReason> {
		let mut negotiation_context = self.0.into_negotiation_context();

		let tx_to_validate = Transaction {
			version: negotiation_context.base_tx.version,
			lock_time: negotiation_context.base_tx.lock_time,
			input: negotiation_context.inputs.values().map(|p| p.input.clone()).collect(),
			output: negotiation_context.outputs.values().cloned().collect(),
		};

		// The receiving node:
		// MUST fail the negotiation if:

		// - the peer's total input satoshis is less than their outputs
		let total_input_amount: u64 = negotiation_context.inputs.values().map(|p| p.prev_output.value).sum();
		let total_output_amount = tx_to_validate.output.iter().map(|output| output.value).sum();
		if total_input_amount < total_output_amount {
			return Err(AbortReason::OutputsExceedInputs);
		}

		// - there are more than 252 inputs
		// - there are more than 252 outputs
		if negotiation_context.inputs.len() > MAX_INPUTS_OUTPUTS_COUNT ||
			negotiation_context.outputs.len() > MAX_INPUTS_OUTPUTS_COUNT {
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
		if negotiation_context.holder_is_initiator {
			let non_initiator_fees_contributed: u64 = negotiation_context.non_initiator_outputs_contributed().map(|output| output.value).sum::<u64>() -
				negotiation_context.non_initiator_inputs_contributed().map(|input| input.prev_output.value).sum::<u64>();
			let non_initiator_contribution_weight = negotiation_context.non_initiator_inputs_contributed().count() as u64 * INPUT_WEIGHT +
				negotiation_context.non_initiator_outputs_contributed().count() as u64 * OUTPUT_WEIGHT;
			let required_non_initiator_contribution_fee = negotiation_context.feerate_sat_per_kw as u64 * 1000 / non_initiator_contribution_weight;
			if non_initiator_fees_contributed < required_non_initiator_contribution_fee {
				return Err(AbortReason::InsufficientFees);
			}
		} else {
			// if is the non-initiator:
			// 	- the initiator's fees do not cover the common fields (version, segwit marker + flag,
			// 		input count, output count, locktime)
			let initiator_fees_contributed: u64 = negotiation_context.initiator_outputs_contributed().map(|output| output.value).sum::<u64>() -
				negotiation_context.initiator_inputs_contributed().map(|input| input.prev_output.value).sum::<u64>();
			let initiator_contribution_weight = negotiation_context.initiator_inputs_contributed().count() as u64 * INPUT_WEIGHT +
				negotiation_context.initiator_outputs_contributed().count() as u64 * OUTPUT_WEIGHT;
			let required_initiator_contribution_fee = negotiation_context.feerate_sat_per_kw as u64 * 1000 / initiator_contribution_weight;
			let tx_common_fields_weight = (4 /* version */ + 4 /* locktime */ + 1 /* input count */ + 1 /* output count */) * WITNESS_SCALE_FACTOR as u64 + 2 /* segwit marker + flag */;
			let tx_common_fields_fee = negotiation_context.feerate_sat_per_kw as u64 * 1000 / tx_common_fields_weight;
			if initiator_fees_contributed < tx_common_fields_fee + required_initiator_contribution_fee {
				return Err(AbortReason::InsufficientFees);
			}
		}

		return Ok(tx_to_validate)
	}
}

impl InteractiveTxStateMachine<TheirTxComplete> {
	fn send_tx_complete(self) -> InteractiveTxStateMachineResult<NegotiationComplete> {
		match self.build_transaction() {
			Ok(tx) => Ok(InteractiveTxStateMachine(NegotiationComplete(tx))),
			Err(e) => Err(InteractiveTxStateMachine(NegotiationAborted(e))),
		}
	}
}

impl InteractiveTxStateMachine<Negotiating> {
	fn receive_tx_complete(self) -> InteractiveTxStateMachine<TheirTxComplete> {
		InteractiveTxStateMachine(TheirTxComplete(self.0.0))
	}

	fn send_tx_complete(self) -> InteractiveTxStateMachine<OurTxComplete> {
		// TODO: Should we validate before transitioning states? If so, do we want to abort negotiation
		// if our current transaction state is invalid?
		InteractiveTxStateMachine(OurTxComplete(self.0.0))
	}
}

impl InteractiveTxStateMachine<OurTxComplete> {
	fn receive_tx_complete(self) -> InteractiveTxStateMachineResult<NegotiationComplete> {
		match self.build_transaction() {
			Ok(tx) => Ok(InteractiveTxStateMachine(NegotiationComplete(tx))),
			Err(e) => Err(InteractiveTxStateMachine(NegotiationAborted(e))),
		}
	}
}

enum ChannelMode {
	Negotiating(InteractiveTxStateMachine<Negotiating>),
	OurTxComplete(InteractiveTxStateMachine<OurTxComplete>),
	TheirTxComplete(InteractiveTxStateMachine<TheirTxComplete>),
	NegotiationComplete(InteractiveTxStateMachine<NegotiationComplete>),
	NegotiationAborted(InteractiveTxStateMachine<NegotiationAborted>),
	Indeterminate,
}

impl Default for ChannelMode {
	fn default() -> Self { Indeterminate }
}

pub(crate) struct InteractiveTxConstructor<ES: Deref> where ES::Target: EntropySource {
	mode: ChannelMode,
	channel_id: [u8; 32],
	is_initiator: bool,
	entropy_source: ES,
	inputs_to_contribute: Vec<TxInputWithPrevOutput>,
	outputs_to_contribute: Vec<TxOut>,
}

pub(crate) enum InteractiveTxMessageSend {
	TxAddInput(msgs::TxAddInput),
	TxAddOutput(msgs::TxAddOutput),
	TxComplete(msgs::TxComplete),
}

// TODO: `InteractiveTxConstructor` methods should return an `Err` when the state machine itself
// errors out. There are two scenarios where that may occur: (1) Invalid data; causing negotiation
// to abort (2) Illegal state transition. Check spec to see if it dictates what needs to happen
// if a node receives an unexpected message.
impl<ES: Deref> InteractiveTxConstructor<ES> where ES::Target: EntropySource {
	pub(crate) fn new(
		entropy_source: ES, channel_id: [u8; 32], feerate_sat_per_kw: u32, require_confirmed_inputs: bool,
		is_initiator: bool, base_tx: Transaction, did_send_tx_signatures: bool,
		inputs_to_contribute: Vec<TxInputWithPrevOutput>, outputs_to_contribute: Vec<TxOut>,
	) -> (Self, Option<InteractiveTxMessageSend>) {
		let initial_state_machine = InteractiveTxStateMachine::new(
			feerate_sat_per_kw, require_confirmed_inputs, is_initiator, base_tx,
			did_send_tx_signatures
		);
		let mut constructor = Self {
			mode: ChannelMode::Negotiating(initial_state_machine),
			channel_id,
			is_initiator,
			entropy_source,
			inputs_to_contribute,
			outputs_to_contribute,
		};
		let message_send = if is_initiator {
			Some(constructor.generate_message_send())
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
	fn generate_message_send(&mut self) -> InteractiveTxMessageSend {
		if let Some(input_with_prevout) = self.inputs_to_contribute.pop() {
			let serial_id = self.generate_local_serial_id();

			let mode = core::mem::take(&mut self.mode);
			self.mode =	match mode {
				ChannelMode::Negotiating(c) => ChannelMode::Negotiating(
					c.send_tx_add_input(serial_id, input_with_prevout.input, input_with_prevout.prev_output)
				),
				ChannelMode::TheirTxComplete(c) => ChannelMode::Negotiating(
					c.send_tx_add_input(serial_id, input_with_prevout.input, input_with_prevout.prev_output)
				),
				_ => mode,
			};

			InteractiveTxMessageSend::TxAddInput(msgs::TxAddInput {
				channel_id: self.channel_id,
				serial_id,
				// TODO: Needs real transaction and prevout
				prevtx: msgs::TransactionU16LenLimited(Transaction { version: 0, lock_time: bitcoin::PackedLockTime::ZERO, input: vec![], output: vec![]}),
				prevtx_out: 0,
				sequence: Sequence::ENABLE_RBF_NO_LOCKTIME.into(),
			})
		} else if let Some(output) = self.outputs_to_contribute.pop() {
			let serial_id = self.generate_local_serial_id();
			let mode = core::mem::take(&mut self.mode);
			self.mode =	match mode {
				ChannelMode::Negotiating(c) => ChannelMode::Negotiating(
					c.send_tx_add_output(serial_id, output.clone())
				),
				ChannelMode::TheirTxComplete(c) => ChannelMode::Negotiating(
					c.send_tx_add_output(serial_id, output.clone())
				),
				_ => mode,
			};
			InteractiveTxMessageSend::TxAddOutput(msgs::TxAddOutput {
				channel_id: self.channel_id,
				serial_id,
				sats: output.value,
				script: output.script_pubkey,
			})
		} else {
			// TODO: Double check that we can transition back to Negotiating.
			self.send_tx_complete();
			InteractiveTxMessageSend::TxComplete(msgs::TxComplete { channel_id: self.channel_id })
		}
	}

	pub(crate) fn receive_tx_add_input(&mut self, transaction_input: &msgs::TxAddInput, confirmed: bool) -> InteractiveTxMessageSend {
		let mode = core::mem::take(&mut self.mode);
		let state_machine = match mode {
			ChannelMode::Negotiating(c) => c.receive_tx_add_input(transaction_input, confirmed),
			ChannelMode::OurTxComplete(c) => c.receive_tx_add_input(transaction_input, confirmed),
			_ => Err(InteractiveTxStateMachine(NegotiationAborted(AbortReason::CounterpartyAborted))), // TODO: Use actual abort reason.
		}.unwrap(); // TODO
		self.mode = ChannelMode::Negotiating(state_machine);
		self.generate_message_send()
	}

	pub(crate) fn receive_tx_remove_input(&mut self, serial_id: SerialId) -> InteractiveTxMessageSend {
		let mode = core::mem::take(&mut self.mode);
		let state_machine = match mode {
			ChannelMode::Negotiating(c) => c.receive_tx_remove_input(serial_id),
			ChannelMode::OurTxComplete(c) => c.receive_tx_remove_input(serial_id),
			_ => Err(InteractiveTxStateMachine(NegotiationAborted(AbortReason::CounterpartyAborted))), // TODO: Use actual abort reason.
		}.unwrap(); // TODO
		self.mode = ChannelMode::Negotiating(state_machine);
		self.generate_message_send()
	}

	pub(crate) fn receive_tx_add_output(&mut self, serial_id: SerialId, output: TxOut) -> InteractiveTxMessageSend {
		let mode = core::mem::take(&mut self.mode);
		let state_machine = match mode {
			ChannelMode::Negotiating(c) => c.receive_tx_add_output(serial_id, output),
			ChannelMode::OurTxComplete(c) => c.receive_tx_add_output(serial_id, output),
			_ => Err(InteractiveTxStateMachine(NegotiationAborted(AbortReason::CounterpartyAborted))), // TODO: Use actual abort reason.
		}.unwrap(); // TODO
		self.mode = ChannelMode::Negotiating(state_machine);
		self.generate_message_send()
	}

	pub(crate) fn receive_tx_remove_output(&mut self, serial_id: SerialId) -> InteractiveTxMessageSend {
		let mode = core::mem::take(&mut self.mode);
		let state_machine = match mode {
			ChannelMode::Negotiating(c) => c.receive_tx_remove_output(serial_id),
			ChannelMode::OurTxComplete(c) => c.receive_tx_remove_output(serial_id),
			_ => Err(InteractiveTxStateMachine(NegotiationAborted(AbortReason::CounterpartyAborted))), // TODO: Use actual abort reason.
		}.unwrap(); // TODO
		self.mode = ChannelMode::Negotiating(state_machine);
		self.generate_message_send()
	}

	pub(crate) fn send_tx_complete(&mut self) {
		let mode = core::mem::take(&mut self.mode);
		self.mode = match mode {
			ChannelMode::Negotiating(c) => { ChannelMode::OurTxComplete(c.send_tx_complete()) }
			ChannelMode::TheirTxComplete(c) => {
				match c.send_tx_complete() {
					Ok(c) => ChannelMode::NegotiationComplete(c),
					Err(c) => ChannelMode::NegotiationAborted(c)
				}
			}
			_ => mode
		}
	}

	pub(crate) fn receive_tx_complete(&mut self) -> Option<InteractiveTxMessageSend> {
		let mode = core::mem::take(&mut self.mode);
		let mut message_send = None;
		match mode {
			ChannelMode::Negotiating(c) => {
				let their_tx_complete = c.receive_tx_complete();
				self.mode = ChannelMode::TheirTxComplete(their_tx_complete);
				message_send = Some(self.generate_message_send());
			}
			ChannelMode::OurTxComplete(c) => {
				self.mode = match c.receive_tx_complete() {
					Ok(c) => ChannelMode::NegotiationComplete(c),
					Err(c) => ChannelMode::NegotiationAborted(c)
				};
			}
			_ => self.mode = mode,
		};
		message_send
	}

	pub(crate) fn abort_negotation(&mut self, reason: AbortReason) {
		let mode = core::mem::take(&mut self.mode);
		match mode {
			ChannelMode::Negotiating(c) => c.abort_negotiation(reason),
			ChannelMode::OurTxComplete(c) => c.abort_negotiation(reason),
			ChannelMode::TheirTxComplete(c) => c.abort_negotiation(reason),
			_ => self.mode = mode, // TODO: Return error
		};
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

