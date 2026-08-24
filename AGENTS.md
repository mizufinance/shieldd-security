# Shieldd formal engineering instructions

This repository owns formal specifications, generators, generated evidence, and
formal CI. Runtime Shieldd changes belong in the Shieldd repository and must be
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

More specific rules under `tools/gnark/lean/AGENTS.md` remain authoritative for
Lean and generator work.

