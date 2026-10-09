# Shieldd security

This repository verifies selected properties of the exact Shieldd revision in
`shieldd.lock`. The current target is PR160 commit
`844389ee069e1fb2e576708842d0b389b4d9a44a`. The reduced delivery has an actual
matched permanent-spend Clean/direct Lean comparison and a reviewed direct Lean
decision, ordered 64-field projection equality/injectivity, and five canonical
permanent-spend gate theorems with full premise/axiom audits. Four F17 omission
controls are reused through an explicit source/field correspondence. Full circuit,
key, caller and permanent-state replay evidence remains open.
Older diagnostic receipts retain their original source scope. Runtime code and
test hooks belong in Shieldd. Formal circuit
specifications live in `circuits/`; the state model and replay adapter live in `state/`.
The circuit lane proves range and Transfer volume arithmetic over emitted Pari
rows. The state lane checks a bounded Quint model and replays real Rust snapshot,
freeze, cache, rollback and storage-reopen cases. These are scoped assurance paths.

Run `python security.py check` for the current-suite policy check. The
`circuits` and `state` commands use the clean checkout at `.work/shieldd-current`.
The narrow route is `python security.py circuits --scope transfer-slice --source
<exact-clean-checkout> --qualified-receipts <preregistered-qualification>
--candidate-dir <fresh-.work-directory>`. It checks independently qualified
retained artifacts and exact current inputs, regenerates only a candidate whose
bytes must equal the actually audited source, and atomically writes
`.work/results/transfer-slice.json`. Post-link validation requires the independently
retained published receipt SHA. This development receipt does not certify full
Transfer or change any release gate. See [verification boundaries](docs/verification.md).
Run heavy verification entirely inside Linux/WSL, using the pinned toolchains;
see [state replay prerequisites](state/README.md). The fixed checkout path keeps
Cargo dependencies and receipt source identity aligned. Existing pilot recipes and
that checkout still require retargeting to the new pin before execution; the new
source checkout alone does not refresh them. Missing evidence fails closed.
The circuit gate needs Rust 1.95.0 and the Lean toolchain in
`circuits/lean-toolchain`, with dependencies from `circuits/lake-manifest.json`.
The Linux CI workflow contains the exact prerequisite installation and narrow
mathlib cache commands. It retains runtime history to compile the immutable
pre-observation baseline in a disposable directory.
Circuit execution has an 80-minute outer budget with smaller named-stage caps;
warm state replay has 30 minutes. CI bounds cold test compilation and development
key generation separately. These resource limits do not strengthen the claims.
`python security.py release` currently fails because required system claims
remain open. See `assurance.json` and [verification boundaries](docs/verification.md).

Routine CI runs circuit arithmetic and `python security.py state --model-only`.
The latter writes a separate `state-model.json`; it cannot replace the full
runtime result. Manually dispatch the security workflow with `runtime_replay`
to generate all seven current development key families and execute real cache/durability
tests. If the runtime repository is private, CI needs `SHIELDD_READ_TOKEN` with
read access. Runtime, pin, circuit and replay changes require a fresh full run
before any release evidence is considered.

A green policy check is not certification. The seven current circuit families,
proof admission, host durability, Bankd settlement, and Orbis release retain
explicit status. The previous Decaf, gnark and SnarkPack stack is retired.
Its reusable handwritten specifications, models and security findings are retained
as [historical migration inputs](reference/README.md), with all 110 named circuit
requirements accounted for. They do not certify the current runtime. The
[four-lane architecture](docs/verification.md) assigns circuit proofs to Lean,
operational models to Quint/TLC, adversarial protocols to Tamarin, and narrowly
qualified gadget determinacy checks to Picus.
