M12 committed-blinding subgroup boundaries: EXECUTION PASSED; independent review pending.

9 joint legal native+actual PARI row cases: 0, 1, subgroup order-1 across fee/self padding, ordinary/external padding, ordinary/external continuation. Each checks leading one, computed public statement digest(index1), exact committed blinding(index2), canonical relation/layout/digest and every actual row. Three baseline1 cases explicitly rechecked before raw controls.

9 raw controls: subgroup order, order+1, circuit-field modulus-1 in three contexts reject native statement computation and native constraints/actual rows. Exact32byte encodings demonstrate representable circuit-field values >= subgroup order, not Jubjub subgroup scalars reduced modulo that order. Circuit-field modulus itself cannot be represented out-of-range and is not tested. Bad constrained raw values use a public claim computed from a legal reduced-reference witness; failures are not attributed solely to the range guard.

18 single-column positive-first mutations: increment committed column2 and shadow column9 for each legal case. Both map to Circuit(Witness6). Column2 touches/fails exactly row200768; column9 exactly rows200510 and200768. All other coordinates unchanged. These IDs distinguish committed-copy link from shadow reconstruction; they do not establish a universal scalar-bound theorem.

Original row evaluator/dot/compiler/layout/digest unchanged; diagnostics mutate clones. Inverse removal of diagnostic methods/cfg exposure restores exact pinned PARI source. M11 test prefix and sealed packet unchanged. Production snapshot untouched. No upstream/prover/crypto re-audit.

Narrow offline Cargo1.95 ci test passed in41.48s; guarded wall60.07s,2Cargo/2Rayon/1testthread,900s owned-process timeout and4GiB headroom guard; zero swap. Source, diffs, hashes, commands and resource logs retained. Reproduce with replay.py --runtime /absolute/pinned-clean --copy /absolute/freshcopy; installed offline dependency cache required.

Runtime pin844389ee069e1fb2e576708842d0b389b4d9a44a. General arbitrary-assignment subgroup bound, full Transfer completeness/backend/admission/state consequences remain open.
