// This file is Copyright its original authors, visible in version control
// history.
//
// This file is licensed under the Apache License, Version 2.0 <LICENSE-APACHE
// or http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your option.
// You may not use this file except in accordance with one or both of these
// licenses.

use std::collections::{HashMap, HashSet};

use bitcoin::{psbt::Psbt, TxIn, Sequence, Transaction, TxOut, OutPoint};
use crate::ln::interactivetxs::ConstructionState::{Negotiating, NegotiationComplete, NegotiationFailed};

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
}

pub(crate) enum ConstructionState {
    /// We are currently in the process of negotiating the transaction.
    Negotiating,
    /// We have sent a `tx_complete` message and are awaiting the counterparty's.
    OurTxComplete,
    /// We have received a `tx_complete` message and the counterparty is awaiting ours.
    TheirTxComplete,
    /// We have exchanged consecutive `tx_complete` messages with the counterparty and the transaction
    /// negotiation is complete.
    NegotiationComplete,
    /// We have sent a `tx_signatures` message and the counterparty is awaiting ours.
    OurTxSignatures,
    /// We have received a `tx_signatures` message from the counterparty.
    TheirTxSignatures,
    /// The negotiation has failed and cannot be continued.
    NegotiationFailed {
        error: AbortReason
    }
}

struct NegotiationContext {
    channel_id: [u8; 32],
    require_confirmed_inputs: bool,
    holder_is_initiator: bool,
    received_tx_add_input_count: u16,
    received_tx_add_output_count: u16,
    base_tx: Transaction,
    inputs: HashMap<u64, TxIn>,
    prevtx_outpoints: HashSet<OutPoint>,
    outputs: HashMap<u64, TxOut>,
}

pub(crate) struct InteractiveTxConstructor {
    state: ConstructionState,
    context: NegotiationContext
}

/// Constructor
impl InteractiveTxConstructor {
    fn new(channel_id: [u8; 32], require_confirmed_inputs: bool, is_initiator: bool, base_tx: Transaction) -> Self {
        Self {
            state: Negotiating,
            context: NegotiationContext {
                channel_id,
                require_confirmed_inputs,
                holder_is_initiator: is_initiator,
                received_tx_add_input_count: 0,
                received_tx_add_output_count: 0,
                base_tx,
                inputs: HashMap::new(),
                prevtx_outpoints: HashSet::new(),
                outputs: HashMap::new(),
            }
        }
    }
}

/// Operations that only work for [`ConstructionState::Negotiating`] and
/// [`ConstructionState::OurTxComplete`]
impl InteractiveTxConstructor {
    fn receive_tx_add_input(mut self, serial_id: SerialId, msg: TxAddInput, confirmed: bool) {
        match self.state {
            ConstructionState::Negotiating | ConstructionState::OurTxComplete => {
                // - TODO: MUST fail the negotiation if:
                //   - `prevtx` is not a valid transaction
                if !self.is_valid_counterparty_serial_id(serial_id) {
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

                if self.context.require_confirmed_inputs && !confirmed {
                    return self.abort_negotiation(AbortReason::InputsNotConfirmed);
                }

                let transaction = msg.prevtx.into_transaction();

                if let Some(tx_out) = transaction.output.get(msg.prevtx_out as usize) {
                    if !tx_out.script_pubkey.is_witness_program() {
                        // The receiving node:
                        //  - MUST fail the negotiation if:
                        //     - the `scriptPubKey` is not a witness program
                        return self.abort_negotiation(AbortReason::PrevTxOutInvalid);
                    } else if !self.context.prevtx_outpoints.insert(
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

                self.context.received_tx_add_input_count += 1;
                if self.context.received_tx_add_input_count > MAX_RECEIVED_TX_ADD_INPUT_COUNT {
                    // The receiving node:
                    //  - MUST fail the negotiation if:
                    //     - if has received 4096 `tx_add_input` messages during this negotiation
                    return self.abort_negotiation(AbortReason::ReceivedTooManyTxAddInputs);
                }

                if let None = self.context.inputs.insert(serial_id, TxIn {
                    previous_output: OutPoint { txid: transaction.txid(), vout: msg.prevtx_out },
                    sequence: Sequence(msg.sequence),
                    ..Default::default()
                }) {
                    self.state = Negotiating
                } else {
                    // The receiving node:
                    //  - MUST fail the negotiation if:
                    //    - the `serial_id` is already included in the transaction
                    self.abort_negotiation(AbortReason::DuplicateSerialId)
                }
            },
            _ => panic!("No op")
        }
    }

    fn receive_tx_remove_input(&mut self, serial_id: SerialId) {
        match self.state {
            ConstructionState::Negotiating | ConstructionState::OurTxComplete => {
                if !self.is_valid_counterparty_serial_id(serial_id) {
                    return self.abort_negotiation(AbortReason::IncorrectSerialIdParity);
                }

                if let Some(input) = self.context.inputs.remove(&serial_id) {
                    self.context.prevtx_outpoints.remove(&input.previous_output);
                    self.state = Negotiating
                } else {
                    // The receiving node:
                    //  - MUST fail the negotiation if:
                    //    - the input or output identified by the `serial_id` was not added by the sender
                    //    - the `serial_id` does not correspond to a currently added input
                    self.abort_negotiation(AbortReason::SerialIdUnknown)
                }
            }
            _ => { panic!("No op") }
        }
    }

    fn receive_tx_add_output(&mut self, serial_id: u64, output: TxOut) {
        match self.state {
            ConstructionState::Negotiating | ConstructionState::OurTxComplete => {
                // TODO: the sats amount is less than the dust_limit
                self.context.received_tx_add_output_count += 1;
                if self.context.received_tx_add_output_count > MAX_RECEIVED_TX_ADD_OUTPUT_COUNT {
                    // The receiving node:
                    //  - MUST fail the negotiation if:
                    //     - if has received 4096 `tx_add_output` messages during this negotiation
                    return self.abort_negotiation(AbortReason::ReceivedTooManyTxAddOutputs);
                }

                if output.value > MAX_MONEY {
                    // The receiving node:
                    // - MUST fail the negotiation if:
                    //		- the sats amount is greater than 2,100,000,000,000,000 (MAX_MONEY)
                    return self.abort_negotiation(AbortReason::ExceededMaximumSatsAllowed);
                }

                if let None = self.context.outputs.insert(serial_id, output) {
                    self.state = Negotiating
                } else {
                    // The receiving node:
                    //  - MUST fail the negotiation if:
                    //    - the `serial_id` is already included in the transaction
                    self.abort_negotiation(AbortReason::DuplicateSerialId)
                }
            }
            _ => { panic!("No op") }
        }
    }

    fn send_tx_add_input(&mut self, serial_id: u64, input: TxIn) {
        self.context.inputs.insert(serial_id, input);
        self.state = Negotiating;
    }

    pub(crate) fn send_tx_add_output(&mut self, serial_id: u64, output: TxOut) {
        self.context.outputs.insert(serial_id, output);
        self.state = Negotiating;
    }

    fn receive_tx_abort(&mut self) {
        todo!();
    }

    pub(crate) fn send_tx_abort(&mut self) {
        // A sending node:
        // 	- MUST NOT have already transmitted tx_signatures
        // 	- SHOULD forget the current negotiation and reset their state.
        todo!();
    }

    fn is_valid_counterparty_serial_id(&self, serial_id: SerialId) -> bool {
        // A received `SerialId`'s parity must match the role of the counterparty.
        self.context.holder_is_initiator == !serial_id.is_valid_for_initiator()
    }

    fn abort_negotiation(&mut self, error: AbortReason) {
        match self.state {
            ConstructionState::Negotiating | ConstructionState::OurTxComplete => {
                self.state = NegotiationFailed { error }
            },
            _ => panic!("No op")
        }
    }
}

/// Operations that only work for [`ConstructionState::OurTxComplete`] and
/// [`ConstructionState::TheirTxComplete`]
impl InteractiveTxConstructor {
    fn send_tx_complete(&mut self) {
        match self.state {
            ConstructionState::OurTxComplete | ConstructionState::TheirTxComplete => {
                self.state = NegotiationComplete
            }
            _ => { panic!("No op") }
        }
    }
}

/// Operations that only work for [`ConstructionState::NegotiationComplete`]
impl InteractiveTxConstructor {
    fn get_psbt(&self) -> Result<Transaction, AbortReason> {
        // Build transaction from inputs & outputs in `NegotiationContext`.
        match self.state {
            ConstructionState::NegotiationComplete => Ok(Transaction {
                version: self.context.base_tx.version,
                lock_time: self.context.base_tx.lock_time,
                input: self.context.inputs.values().cloned().collect(),
                output: self.context.outputs.values().cloned().collect(),
            }),
            _ => { panic!("no op") }
        }
    }
}

