# Shieldd security

This repository verifies selected properties of the exact Shieldd revision in
`shieldd.lock`. Runtime code and test hooks belong in Shieldd. Formal circuit
specifications live in `circuits/`; the state model and replay adapter live in `state/`.
The circuit lane proves range and Transfer volume arithmetic over emitted Pari
rows. The state lane checks a bounded Quint model and replays real Rust snapshot,
freeze, cache, rollback and storage-reopen cases. These are scoped assurance paths.

Run `python security.py check` for the current-suite policy check. The
`circuits` and `state` commands use the clean checkout at `.work/shieldd-current`.
Run heavy verification entirely inside Linux/WSL, using the pinned toolchains;
see [state replay prerequisites](state/README.md). The fixed checkout path keeps
Cargo dependencies and receipt source identity aligned. Missing evidence fails closed.
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
to generate all nine development key families and execute real cache/durability
tests. If the runtime repository is private, CI needs `SHIELDD_READ_TOKEN` with
read access. Runtime, pin, circuit and replay changes require a fresh full run
before any release evidence is considered.

A green policy check is not certification. The nine current circuit families,
proof admission, host durability, Bankd settlement, and Orbis release retain
explicit status. The previous Decaf, gnark and SnarkPack stack is retired.
