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

use super::msgs::TxAddInput;

/// The number of received `tx_add_input` messages during a negotiation at which point the
/// negotiation MUST be failed.
const MAX_RECEIVED_TX_ADD_INPUT_COUNT: u16 = 4096;

/// The number of received `tx_add_output` messages during a negotiation at which point the
/// negotiation MUST be failed.
const MAX_RECEIVED_TX_ADD_OUTPUT_COUNT: u16 = 4096;
const MAX_MONEY: u64 = 2_100_000_000_000_000;

type SerialId = u64;
trait SerialIdExt {
	fn is_valid_for_initiator(&self) -> bool;
}
impl SerialIdExt for SerialId {
	fn is_valid_for_initiator(&self) -> bool { self % 2 == 0 }
}

pub(crate) enum InteractiveTxConstructionError {
	InputsNotConfirmed,
	ReceivedTooManyTxAddInputs,
	ReceivedTooManyTxAddOutputs,
	IncorrectInputSequenceValue,
	IncorrectSerialIdParity,
	SerialIdUnknown,
	DuplicateSerialId,
	PrevTxOutInvalid,
	ExceedMaxiumSatsAllowed,
}

// States
// TODO: ASCII state machine
pub(crate) trait AcceptingChanges {}

/// We are currently in the process of negotiating the transaction.
pub(crate) struct Negotiating;
/// We have sent a `tx_complete` message and are awaiting the counterparty's.
pub(crate) struct OurTxComplete;
/// We have received a `tx_complete` message and the counterparty is awaiting ours.
pub(crate) struct TheirTxComplete;
/// We have exchanged consecutive `tx_complete` messages with the counterparty and the transaction
/// negotiation is complete.
pub(crate) struct NegotiationComplete;
/// We have sent a `tx_signatures` message and the counterparty is awaiting ours.
pub(crate) struct OurTxSignatures;
/// We have received a `tx_signatures` message from the counterparty
pub(crate) struct TheirTxSignatures;
/// The negotiation has failed and cannot be continued.
pub(crate) struct NegotiationFailed {
	error: InteractiveTxConstructionError,
}

// TODO: Add RBF negotiation

impl AcceptingChanges for Negotiating {}
impl AcceptingChanges for OurTxComplete {}

struct NegotiationContext {
	channel_id: [u8; 32],
	require_confirmed_inputs: bool,
	holder_is_initiator: bool,
	received_tx_add_input_count: u16,
	received_tx_add_output_count: u16,
	inputs: HashMap<u64, TxIn>,
	prevtx_outpoints: HashSet<OutPoint>,
	outputs: HashMap<u64, TxOut>,
	base_tx: Transaction,
}

pub(crate) struct InteractiveTxConstructor<S> {
	inner: Box<NegotiationContext>,
	state: S,
}

impl InteractiveTxConstructor<Negotiating> {
	fn new(channel_id: [u8; 32], require_confirmed_inputs: bool, is_initiator: bool, base_tx: Transaction) -> Self {
		Self {
			inner: Box::new(NegotiationContext {
				channel_id,
				require_confirmed_inputs,
				holder_is_initiator: is_initiator,
				received_tx_add_input_count: 0,
				received_tx_add_output_count: 0,
				inputs: HashMap::new(),
				prevtx_outpoints: HashSet::new(),
				outputs: HashMap::new(),
				base_tx,
			}),
			state: Negotiating,
		}
	}
}

impl<S> InteractiveTxConstructor<S>
	where S: AcceptingChanges {
	fn fail_negotiation(self, error: InteractiveTxConstructionError) ->
	Result<InteractiveTxConstructor<Negotiating>, InteractiveTxConstructor<NegotiationFailed>> {
		Err(InteractiveTxConstructor { inner: self.inner, state: NegotiationFailed { error } })
	}

	fn receive_tx_add_input(mut self, serial_id: SerialId, msg: TxAddInput, confirmed: bool) ->
	Result<InteractiveTxConstructor<Negotiating>, InteractiveTxConstructor<NegotiationFailed>> {
		// - TODO: MUST fail the negotiation if:
		//   - `prevtx` is not a valid transaction
		if !self.is_valid_counterparty_serial_id(serial_id) {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - the `serial_id` has the wrong parity
			return self.fail_negotiation(InteractiveTxConstructionError::IncorrectSerialIdParity);
		}

		if msg.sequence >= 0xFFFFFFFE {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - `sequence` is set to `0xFFFFFFFE` or `0xFFFFFFFF`
			return self.fail_negotiation(InteractiveTxConstructionError::IncorrectInputSequenceValue);
		}

		if self.inner.require_confirmed_inputs && !confirmed {
			return self.fail_negotiation(InteractiveTxConstructionError::InputsNotConfirmed);
		}

		if let Some(tx_out) = msg.prevtx.output.get(msg.prevtx_out as usize) {
			if !tx_out.script_pubkey.is_witness_program() {
				// The receiving node:
				//  - MUST fail the negotiation if:
				//     - the `scriptPubKey` is not a witness program
				return self.fail_negotiation(InteractiveTxConstructionError::PrevTxOutInvalid);
			} else if !self.inner.prevtx_outpoints.insert(OutPoint { txid: msg.prevtx.txid(), vout: msg.prevtx_out }) {
				// The receiving node:
				//  - MUST fail the negotiation if:
				//     - the `prevtx` and `prevtx_vout` are identical to a previously added
				//       (and not removed) input's
				return self.fail_negotiation(InteractiveTxConstructionError::PrevTxOutInvalid);
			}
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - `prevtx_vout` is greater or equal to the number of outputs on `prevtx`
			return self.fail_negotiation(InteractiveTxConstructionError::PrevTxOutInvalid);
		}

		self.inner.received_tx_add_input_count += 1;
		if self.inner.received_tx_add_input_count > MAX_RECEIVED_TX_ADD_INPUT_COUNT {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - if has received 4096 `tx_add_input` messages during this negotiation
			return self.fail_negotiation(InteractiveTxConstructionError::ReceivedTooManyTxAddInputs);
		}

		if let None = self.inner.inputs.insert(serial_id, TxIn {
			previous_output: OutPoint { txid: msg.prevtx.txid(), vout: msg.prevtx_out },
			sequence: Sequence(msg.sequence),
			..Default::default()
		}) {
			Ok(InteractiveTxConstructor { inner: self.inner, state: Negotiating {} })
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - the `serial_id` is already included in the transaction
			self.fail_negotiation(InteractiveTxConstructionError::DuplicateSerialId)
		}
	}

	fn receive_tx_remove_input(mut self, serial_id: SerialId) ->
	Result<InteractiveTxConstructor<Negotiating>, InteractiveTxConstructor<NegotiationFailed>> {
		if !self.is_valid_counterparty_serial_id(serial_id) {
			return self.fail_negotiation(InteractiveTxConstructionError::IncorrectSerialIdParity);
		}

		if let Some(input) = self.inner.inputs.remove(&serial_id) {
			self.inner.prevtx_outpoints.remove(&input.previous_output);
			Ok(InteractiveTxConstructor { inner: self.inner, state: Negotiating {} })
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - the input or output identified by the `serial_id` was not added by the sender
			//    - the `serial_id` does not correspond to a currently added input
			self.fail_negotiation(InteractiveTxConstructionError::SerialIdUnknown)
		}
	}

	fn receive_tx_add_output(mut self, serial_id: u64, output: TxOut) ->
	Result<InteractiveTxConstructor<Negotiating>, InteractiveTxConstructor<NegotiationFailed>> {
		// TODO: the sats amount is less than the dust_limit
		self.inner.received_tx_add_output_count += 1;
		if self.inner.received_tx_add_output_count > MAX_RECEIVED_TX_ADD_OUTPUT_COUNT {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//     - if has received 4096 `tx_add_output` messages during this negotiation
			return self.fail_negotiation(InteractiveTxConstructionError::ReceivedTooManyTxAddOutputs);
		}

		if output.value > MAX_MONEY {
			// The receiving node:
			// - MUST fail the negotiation if:
			//		- the sats amount is greater than 2,100,000,000,000,000 (MAX_MONEY)
			return self.fail_negotiation(InteractiveTxConstructionError::ExceedMaxiumSatsAllowed);
		}

		if let None = self.inner.outputs.insert(serial_id, output) {
			Ok(InteractiveTxConstructor { inner: self.inner, state: Negotiating {} })
		} else {
			// The receiving node:
			//  - MUST fail the negotiation if:
			//    - the `serial_id` is already included in the transaction
			self.fail_negotiation(InteractiveTxConstructionError::DuplicateSerialId)
		}
	}

	pub(crate) fn receive_tx_abort(mut self) -> InteractiveTxConstructor<NegotiationFailed> {
		todo!();
	}

	fn send_tx_add_input(mut self, serial_id: u64, input: TxIn) -> InteractiveTxConstructor<Negotiating> {
		self.inner.inputs.insert(serial_id, input);
		InteractiveTxConstructor { inner: self.inner, state: Negotiating {} }
	}

	pub(crate) fn send_tx_add_output(mut self, serial_id: u64, output: TxOut) -> InteractiveTxConstructor<Negotiating> {
		self.inner.outputs.insert(serial_id, output);
		InteractiveTxConstructor { inner: self.inner, state: Negotiating {} }
	}

	pub(crate) fn send_tx_abort(mut self) -> InteractiveTxConstructor<NegotiationFailed> {
		// A sending node:
		// 	- MUST NOT have already transmitted tx_signatures
		// 	- SHOULD forget the current negotiation and reset their state.
		todo!();
	}

	fn is_valid_counterparty_serial_id(&self, serial_id: SerialId) -> bool {
		// A received `SerialId`'s parity must match the role of the counterparty.
		self.inner.holder_is_initiator == !serial_id.is_valid_for_initiator()
	}
}

impl InteractiveTxConstructor<TheirTxComplete> {
	fn send_tx_complete(self) -> InteractiveTxConstructor<NegotiationComplete> {
		InteractiveTxConstructor {
			inner: self.inner,
			state: NegotiationComplete {}
		}
	}
}

impl InteractiveTxConstructor<OurTxComplete> {
	fn receive_tx_complete(self) -> InteractiveTxConstructor<NegotiationComplete> {
		InteractiveTxConstructor {
			inner: self.inner,
			state: NegotiationComplete {}
		}
	}
}

impl InteractiveTxConstructor<NegotiationComplete> {
	fn get_psbt(&self) -> Result<Transaction, InteractiveTxConstructionError> {
		// Build transaction from inputs & outputs in `NegotiationContext`.
		return Ok(Transaction {
			version: self.context.base_tx.version,
			lock_time: self.context.base_tx.lock_time,
			input: self.context.inputs.values().cloned().collect(),
			output: self.context.outputs.values().cloned().collect(),
		})
	}
}

enum ChannelMode {
	Negotiating(InteractiveTxConstructor<Negotiating>),
	OurTxComplete(InteractiveTxConstructor<OurTxComplete>),
	TheirTxComplete(InteractiveTxConstructor<TheirTxComplete>),
	NegotiationComplete(InteractiveTxConstructor<NegotiationComplete>),
	OurTxSignatures(InteractiveTxConstructor<OurTxSignatures>),
	TheirTxSignatures(InteractiveTxConstructor<TheirTxSignatures>),
	NegotiationFailed(InteractiveTxConstructor<NegotiationFailed>),
}

#[cfg(test)]
mod tests {
	use crate::ln::interactivetxs::ChannelMode::Negotiating;
	use crate::ln::interactivetxs::{ChannelMode, DummyChannel, InteractiveTxConstructor};
	use bitcoin::consensus::encode;
	use bitcoin::Transaction;
	use crate::ln::msgs::TxAddInput;

	struct DummyChannel {
		mode: ChannelMode,
	}

	impl DummyChannel {
		fn new() -> Self {
			let tx: Transaction = encode::deserialize(&hex::decode("020000000001010e0ade\
			f48412e4361325ac1c6e36411299ab09d4f083b9d8ddb55fbc06e1b0c00000000000feffffff0220a107000\
			0000000220020f81d95e040bd0a493e38bae27bff52fe2bb58b93b293eb579c01c31b05c5af1dc072cfee54\
			a3000016001434b1d6211af5551905dc2642d05f5b04d25a8fe80247304402207f570e3f0de50546aad25a8\
			72e3df059d277e776dda4269fa0d2cc8c2ee6ec9a022054e7fae5ca94d47534c86705857c24ceea3ad51c69\
			dd6051c5850304880fc43a012103cb11a1bacc223d98d91f1946c6752e358a5eb1a1c983b3e6fb15378f453\
			b76bd00000000").unwrap()[..]).unwrap();
			Self {
				mode: Negotiating(InteractiveTxConstructor::new(
					[0; 32],
					true,
					true,
					tx
				))
			}
		}
	}

	fn trivial_test() {
		let channel_a = DummyChannel::new();

		match channel_a.mode {
			Negotiating(constructor) => {}
			ChannelMode::OurTxComplete(_) => {}
			ChannelMode::TheirTxComplete(_) => {}
			ChannelMode::NegotiationComplete(_) => {}
			ChannelMode::OurTxSignatures(_) => {}
			ChannelMode::TheirTxSignatures(_) => {}
			ChannelMode::NegotiationFailed(_) => {}
		}
	}
}

