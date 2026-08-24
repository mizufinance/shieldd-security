# Statement Field Map

This is the canonical ordered schema for the single-hash public input seam.
The `Rust symbol`, `Go circuit symbol`, and `Go differential symbol` columns are
machine-checked for live symbols.

| ID | Circuit family | Order | Field group | Rust symbol | Go circuit symbol | Go differential symbol | Status |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `STMT-TRANSFER-ANCHOR` | transfer | 0 | witness anchor | `transfer_statement_fields` | `buildTransferStatementFields` | `ReconstructedTransferStatementFieldsFromWitnessV20` | `composed` |
| `STMT-TRANSFER-OUTPUTS` | transfer | 1-2 | output note commitments | `transfer_statement_fields` | `buildTransferStatementFields` | `ReconstructedTransferStatementFieldsFromWitnessV20` | `composed` |
| `STMT-TRANSFER-BALANCE` | transfer | 3 | computed net-balance commitment encoding; no affine balance witness is serialized | `transfer_statement_fields` | `buildTransferStatementFields` | `ReconstructedTransferStatementFieldsFromWitnessV20` | `composed` |
| `STMT-TRANSFER-ROUTING` | transfer | 4-7 | two routing tags, parameter-set identifier, and recent-position floor | `transfer_statement_fields` | `buildTransferStatementFields` | `ReconstructedTransferStatementFieldsFromWitnessV20` | `composed` |
| `STMT-TRANSFER-SPENDS` | transfer | 8-13 | two input `(nullifier, RK, history_required)` triples | `transfer_statement_fields` | `buildTransferStatementFields` | `ReconstructedTransferStatementFieldsFromWitnessV20` | `composed` |
| `STMT-TRANSFER-ANCHORS` | transfer | 14-15 | asset and compliance anchors | `transfer_statement_fields` | `buildTransferStatementFields` | `ReconstructedTransferStatementFieldsFromWitnessV20` | `composed` |
| `STMT-TRANSFER-CIPHERTEXT` | transfer | 16-35 | detection ciphertext and four encrypted tiers including EPK and `c2` | `transfer_statement_fields` | `buildTransferStatementFields` | `ReconstructedTransferStatementFieldsFromWitnessV20` | `composed` |
| `STMT-TRANSFER-TIMESTAMP` | transfer | 36 | target timestamp | `transfer_statement_fields` | `buildTransferStatementFields` | `ReconstructedTransferStatementFieldsFromWitnessV20` | `composed` |
| `STMT-TRANSFER-METADATA` | transfer | 37-44 | four selected policy hashes and four tier salts; metadata timestamp equals field 36 | `transfer_statement_fields` | `buildTransferStatementFields` | `ReconstructedTransferStatementFieldsFromWitnessV20` | `composed` |
| `STMT-NOTE-RESHAPE-BASE` | NoteReshape | 0..n | anchor, output commitments, balance commitment, input nullifier/RK pairs | `note_reshape_statement_fields` | `NoteReshapeCircuit` | `ReconstructedNoteReshapeStatementFieldsFromWitnessV6` | `composed` |
| `STMT-SHIELDED-ICS20-BASE` | shielded ICS-20 withdrawal | 0-9 | anchor, change commitment, balance commitment, recent-position floor, and two input `(nullifier, RK, history_required)` triples | `shielded_ics20_withdrawal_statement_fields` | `hashShieldedIcs20WithdrawalStatement` | `ReconstructedShieldedIcs20WithdrawalStatementFieldsFromWitnessV12` | `composed` |
| `STMT-SHIELDED-ICS20-EFFECT` | shielded ICS-20 withdrawal | 10-20 | asset/compliance anchors, target timestamp, outbound asset/amount, withdrawal effect hash limbs, routing tag, and routing parameter-set identifier | `shielded_ics20_withdrawal_statement_fields` | `hashShieldedIcs20WithdrawalStatement` | `ReconstructedShieldedIcs20WithdrawalStatementFieldsFromWitnessV12` | `composed` |
