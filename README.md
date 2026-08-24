# Shieldd formal verification

This repository owns Shieldd's formal specifications, generated Lean evidence,
and every formal-verification CI gate. Shieldd itself owns runtime code,
circuits, witnesses, proving material, and ordinary compile/prove/verify smoke
tests; it never runs Lean, Alloy, Picus, F*, or formal evidence replay.

`shieldd.lock` names the exact Shieldd commit certified by this repository. The
formal runner checks out that commit and overlays the paths listed in
`formal-files.json`, preserving the source-relative layout expected by the
generators and proofs.

## Commands

```sh
python3 formal.py gate soundness --mode affected
python3 formal.py gate soundness --mode release
python3 formal.py gate snarkpack --mode full
python3 formal.py evidence refresh --all
python3 formal.py evidence refresh --check --all
```

Use `--shieldd-source` for a local clone and `--shieldd-ref` for a specific
commit while preparing a coordinated Shieldd/formal change. Read-only gates
reuse an independently copied composed checkout; Cargo, Go, Lean, and mirror
caches survive later gates. A refresh runs in a disposable writable checkout,
verifies the regenerated closure, and only then promotes changed formal-owned
evidence. Failed generation leaves the repository untouched.

Only the four certified SR1CS inputs declared in `formal-files.json` are
materialized. A local Shieldd checkout supplies independent copies after their
size and SHA-256 match the locked commit's LFS pointers; remote runs use one
targeted Git LFS request backed by the cached Shieldd mirror. No formal command
hydrates the full LFS history.

PR gates run only for changes in this repository. The monthly workflow performs
the full replay against the locked Shieldd commit.
