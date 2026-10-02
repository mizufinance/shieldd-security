# Verification boundaries

Lean is the proof foundation. The circuit pilot targets 128-bit range/comparison
and volume arithmetic against the exact patched Pari constraints. Soundness must
quantify arbitrary satisfying field assignments; honest witness tests are separate.
Exported row identity alone does not prove the compiler-to-specification join.
The volume arithmetic theorem must discharge caller-provided outbound bounds.
Full-family relations, hash/Merkle semantics and verification-key correspondence
remain separate obligations.

The circuit gate must join the actual Transfer caller's output amount to volume
arithmetic, prove integer addition without wrap and inclusive comparison, and
cover legal padding (whose candidate range remains unconditional). Read-only
observations preserve the original InputLayout; compare against the immutable
pre-observation relation. Completeness and compiler extension/projection are
separate from the all-assignment soundness implication. Required controls cover
bit/range reconstruction, comparison, candidate range, public/constant links,
deferred squares, altered columns/field/layout and stale source identity.

Quint models paired user/asset snapshots and freeze epochs. A finite model check
records its bounds and backend. Real Rust trace replay must call actual admission,
cached delivery and persistent storage operations. This is model-based testing,
not a Rust refinement proof. Freeze/unfreeze, inclusive expiry, zero grace,
equal timestamps, paired roots, rollback/restart and bounded pruning require
independent cases; the 64-entry limit bounds obsolete deletions per block, not
retained history.

Replay compares outcomes and storage projection after each step. Cache coverage
requires an actual verified artifact consumed through transaction delivery after
freezing an unrelated user. Restart closes storage and reopens the same database;
constructing another host around live storage does not suffice. Include actual
Rust controls for epoch bypass, mixed-pair acceptance and rollback failure.
Time and epochs never wrap modulo the finite model domain.

Use Commonware's implementation while recording exact upstream and patch
identities. Reuse its cryptographic backend rather than maintaining duplicate
Decaf, gnark or SnarkPack proofs. This does not transfer Shieldd's obligations:
Shieldd owns circuit relations, caller/input mappings, field-to-integer arithmetic
and the state-dependent acceptance of transactions. The baseline uses upstream
`1a56762927a8ad3300e0594886c28c59d9801769` with Shieldd's exact vendored patches;
runtime `scripts/commonware.py` must reproduce their provenance at the final lock.
The Lean kernel checks the stated row theorems. Exporting the real relation,
canonical coefficient translation and matching its observed columns remain
explicit trusted joins. Compiler regression controls qualify only their finite
fixtures. Backend cryptographic soundness, transcript/setup assumptions and
verification-key correspondence remain outside these two pilots.

The initial Clean source/API feasibility review was followed by an actual matched
four-gate spike at the pinned Clean revision `fba2a29f5e36420d797c1de118ac9f11f23b819e`
using Lean 4.33.1. Both implementations and finite F17 controls passed their scoped
kernel audits. Direct Lean was chosen for reduced-slice maintenance and coverage,
not a speed ranking: the arms have different theorem/audit workloads and reached
closures, share algebraic proofs, and did not control OS caches. The canonical
package remains on Lean 4.30.0. The runtime compiler/row bridge is still an explicit
assumption in either approach. See [current results and retained evidence](pr160-transfer-slice.md).

Quint is the single state specification language; its TLC backend uses TLA+
model checking without maintaining a second handwritten TLA+ specification.
Lean remains appropriate for unbounded field and integer arithmetic theorems.

`assurance.json` is the claim register. Pilot results bind the runtime commit,
security source digest, tools/build settings and limits. Dirty runs are diagnostic;
stale or missing evidence cannot establish release eligibility. Negative controls
must detect the intended semantic defect, not merely a build error or timeout.
Full-system certification is not established.

The broader circuit/state delivery, which this reduced slice does not close, requires both scoped commands executed against a clean, retrievable
runtime commit, fault-sensitive controls and independent implementation review.
Runtime changes live in Shieldd; generated outputs and logs live in ignored
`.work` or CI artifacts. Keep the one-heavy-job/one-Lean-process resource policy
from AGENTS.md. The migration plan and broad architecture proposal have been
consolidated here; no legacy replay stack is maintained.
