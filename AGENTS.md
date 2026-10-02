# Shieldd security engineering instructions

This repository owns formal specifications, generators, generated evidence, and
formal CI, and security campaigns. Runtime Shieldd changes belong in the Shieldd repository and must be
referenced by an exact `shieldd.lock` commit.

- Never hand-edit generated Lean or evidence to clear a gate. Fix the source,
  generator, specification, or proof, then use the atomic evidence refresh.
- Keep handwritten and generated changes in separate commits when practical.
- Run exactly one `lake` process at a time with `LEAN_NUM_THREADS=1`.
- Use the narrowest named Lean module during development; full replay is a
  release or scheduled operation.
- Do not commit `.lake`, downloaded theorem-prover toolchains, compiler caches,
  logs, or composed Shieldd workspaces.
- A certification result is meaningful only for the full SHA in
  `shieldd.lock`; never certify a branch name or a dirty working tree.

Keep this repository small: one CLI, one claim register, one Lean package, and
models backed by real runtime replay. Add infrastructure only for a live claim.

Lean proofs must use finite heartbeats, small reusable lemmas and symbolic
recurrences instead of unrolled wide constraint walks. Never use `sorry`,
`admit`, or new unsound axioms. Audit theorem conclusions, premises and axioms.
Monitor builds and stop this task's jobs on memory pressure. Run only one heavy
verification job at a time across agents (Lean, Cargo, or model checking).

Evidence must distinguish proof, bounded model checking, runtime testing and
assumptions. A hash establishes identity, not semantic correspondence. Negative
controls count only when the intended semantic failure is observed; a compiler
error, missing dependency or timeout is not a successful control.

