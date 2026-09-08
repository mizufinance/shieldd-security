# Shieldd security

This repository owns Shieldd's formal specifications, generated Lean evidence,
formal CI, and bounded decoder fuzz campaigns. Shieldd itself owns runtime code,
circuits, witnesses, proving material, and ordinary compile/prove/verify smoke
tests; it never runs Lean, Alloy, Picus, F*, or formal evidence replay.

`shieldd.lock` selects an exact candidate; it does not certify that commit. The
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

Refresh validation reruns every generated-output drift check plus the generator
mtime smoke test. Formal soundness gates retain the exhaustive generator
mutation suite; the monthly release gate therefore independently rechecks a
refreshed evidence tree before accepting it.

On Windows, the runner keeps shell orchestration in WSL but runs the coverage
extractor and filesystem-heavy Python catalog/completeness checks natively.
Temporary compiled manifests and isolated semantic payloads live under
`.work/gate-tmp` and are removed when the gate exits.

Only the four certified SR1CS inputs declared in `formal-files.json` are
materialized. A local Shieldd checkout supplies independent copies after their
size and SHA-256 match the locked commit's LFS pointers; remote runs use one
targeted Git LFS request backed by the cached Shieldd mirror. No formal command
hydrates the full LFS history.

PR gates run only for changes in this repository. The monthly workflow performs
the full replay against the locked Shieldd commit.

## Decoder assurance

```sh
python3 security.py fuzz --seconds 60
python3 decoder_contract.py
```

Shieldd owns the single native decoder target, its independent reference oracle,
and small regression seeds. This repository owns campaign scheduling, persistent
corpora, findings, resource limits, and verification reports. A minimized finding
becomes an ordinary Shieldd regression before a runtime fix is accepted.

PR fuzzing replays every curated seed before a 60-second ASan campaign; scheduled
and manual runs allow 30 minutes. Runs use one fuzz worker, a 2 GiB RSS limit,
15 seconds per input, and 100 MiB for corpus and logs. Reports record the exact
candidate, tool versions, lockfile hash, seed hashes, limits, and outcome.

The focused F* job copies the exact wrapper and canonical comparison modules
from the locked candidate into a dependency-free extraction crate, recording
source hashes. It checks wrapper roundtrip, digest/cap rejection, truncated-header and
unsupported-domain rejection, plus canonical equality lemmas against fresh hax output. This covers parsing and byte comparison, not
Arkworks decoding, group/subgroup validity, allocation, or circuit soundness.
Native fuzzing remains necessary for those implementation boundaries.

`certification.json` separates the candidate from full certification. Known
circuit/evidence failures remain visible in the existing formal jobs; focused
proof or fuzz success must never be reported as full certification. Runtime
owners review semantics and regressions; security owners review proof assumptions,
corpus quality, and campaigns. Shared ownership does not duplicate the target.
