M6 exact maintained routing construction, runtime pin 844389ee069e1fb2e576708842d0b389b4d9a44a.

TransferRoutingBranchCompletion.constructed_routing_semantics constructs parameter hash, permutation, meaningful-slot selection, all 32 selected digits, and both binary tags for every legal input (rp <= up <= 32). No RoutingSem, desired output equation, or hash injectivity premise. Six routing fields are canonical under CanonicalCrypto and an explicit height bound; base canonicality then preserves the full CanonicalWitness. Whole-record restoration covers all non-routing fields. Five semantic refusal controls cover wrong parameter hash, reversed/oversized precision, oversized tag, and changed selected bit. Existing unchanged RoutingTagSemantics helpers provide binary-digit and length bounds; they are reused maintained results, not original M6 results.

Lean: 16 original named theorems audited, only propext/Quot.sound; no sorryAx, custom axiom, or Classical.choice. Final recheck logs/results retained separately. Earlier source attempts and failures are retained under development-evidence; partial failed audits are not accepted.

Native: 2 existing unchanged routing::tests pass. The positive matrix is 8 nonces x 5 precision pairs x 2 regulated values x 2 change values = 160 component circuit cases, with 320 tag values. Both permutations occur among those 8 nonces. Precision pairs: (0,0), (0,32), (1,1), (7,19), (32,32). The second test starts from a constructed case, checks 7 witness mutations, regulated/change/nonce changes, meaningful receiver binding, irrelevant sender substitution, and recomputed-hash reversed precision. This is finite native component satisfaction, not a parameterized native assignment proof.

Recheck in the existing unchanged dependency project:
python3 outputs/mac-routing-completion/recheck.py --project work/mac-volume-completion/project --log work/mac-routing-completion/sealed-recheck.log

To reconstruct that project use the M5 packet preparation instructions, then copy the 3 additional byte-hashed Routing*.lean inputs and compile them in listed order with lake +leanprover/lean4:v4.30.0 env lean -j1 -M2048 -R PROJECT -o PROJECT/.lake/build/lib/lean/ShielddSecurity/NAME.olean PROJECT/ShielddSecurity/NAME.lean. No additional Mathlib cache roots are needed. All 35 maintained inputs and exact inherited revisions are included in input-identities.json/maintained-inputs.

Native replay in the retained disposable M3/M5 harness (source hashes and added Mac-only modules recorded in native-inputs.json):
CARGO_BUILD_JOBS=2 RAYON_NUM_THREADS=2 cargo +1.95.0 test --locked --offline --manifest-path work/mac-branches/runtime-harness/Cargo.toml -p shieldd-sdk-circuits --profile ci --lib routing::tests:: -- --nocapture --test-threads=1
The underlying routing.rs is unchanged; a fresh pinned checkout can run the same filter with its own test-count context. The recorded 53 filtered tests include the two previously added Mac harness modules. Commonware cfg warnings are retained.

Boundary: exact maintained semantic construction and conditional canonicality, source formula comparison, finite native component replay. No full Transfer circuit assignment, arbitrary row soundness, PARI relation satisfaction, backend cryptographic soundness, Rust decoding refinement, or accepted-state consequence is claimed. Transfer remains open until the Windows-owned joined obligations are closed. Newly authored proofs await independent review.
