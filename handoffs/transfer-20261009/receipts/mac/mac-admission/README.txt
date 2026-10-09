Mac admission packet — original M2 model and manual source contract
Runtime 844389ee069e1fb2e576708842d0b389b4d9a44a

Start with source-contract.txt and test-inventory.txt. The first packet establishes
15 narrow Lean model theorems and 55 dual-solver predicate checks, alongside the
actual source path and explicit joins required before integration. It awaits
independent review; it is not a completed Transfer/circuit/backend certification.

Artifacts:
Admission.lean          Original proof/model source; no Shieldd/mathlib imports.
lean-audit.txt          Final successful named-theorem axiom audit.
source-map.json        Exact 39 files / 88 regions, hashes and original excerpts.
check_packet.py        Reproduction runner, read-only to the runtime snapshot.
queries/               All 55 original SMT queries.
results.json           Exact commands, solver outputs/models and source checks.
source-contract.txt    Implemented guarantees, assumptions and correspondence.
test-inventory.txt     Existing source tests, fixture axes and focused gaps.
tool-identities.json   Installed tools/direct imports and final resource status.
development-evidence/  Failed elaboration attempts retained as failed evidence.
packet-sha256.json     Relative path/size/SHA256 inventory, excluding itself.

Reproduce from /Users/antoinecyr/Documents/Codex/2026-10-08/can:

python3 outputs/mac-admission/check_packet.py --runtime work/runtime-snapshot --results work/mac-admission/review-run

Or just the fresh Lean model:

lean +leanprover/lean4:v4.30.0 -j1 -M1024 outputs/mac-admission/Admission.lean

The runner first requires the exact clean runtime SHA and source-map identities;
it never refreshes those expected hashes. It recompiles this source, checks the
axiom output and runs the SMT inputs sequentially. Z3/cvc5 binaries are explicitly
selected to avoid the Picus PATH wrapper. Each solver has a 10-second limit and a
15-second subprocess bound; Lean has finite heartbeats and a 30-second runner
timeout. Use a fresh result directory to keep previous evidence.

Final result: 15 Lean theorems; 26 UNSAT and 29 SAT cases in both solvers,
110 successful solver calls, zero failed final checks. SAT includes omission
controls, actual modeled receipt boundaries, signed-net and a positive baseline;
it does not mean 29 runtime defects. Canonicality, cryptography, fields and byte
identities are explicitly abstracted. No Rust tests/proof gates were run.

Development history:
Attempt 01 failed before complete elaboration: reserved identifier `local` and
unbound `hash` resolving to Lean's built-in hash. Renaming to keyFor/digestFn
produced a clean successful model (attempt 02). The later two-state control's
attempt 03 failed to synthesize Decidable for an opaque predicate; its partial
diagnostic axiom output included sorryAx and was NOT accepted. Unfolding preAt
fixed it (attempt 04). The final model subsequently added an explicit claim-opening
association hypothesis and refined documentation/source-map coverage; the final
complete qualified-run recompiled all 15 theorems with no sorryAx and reran all
55 queries. Failed logs/sources are preserved; none count as rejection controls.

Resource/coordination: one sequential local verification lane, Lean -j1 -M1024,
no package downloads, Cargo builds, registry setup or other processes terminated.
No jobs remain running at packet completion. Heavy verification slot is returned
to the parent coordinator. The desktop session stayed paused/unmessaged. The
unpublished Windows caller/role0 packet remains an external comparison dependency.
