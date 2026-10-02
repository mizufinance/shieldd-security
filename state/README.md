# Snapshot and freeze checks

`python security.py state` runs the model and runtime checks against the clean
pinned checkout at `.work/shieldd-current`. Run the whole command inside Linux
or the existing Ubuntu WSL environment so cancellation owns every subprocess.
`python security.py state --model-only` runs the finite model and exports traces
to a separate model-only receipt; it does not establish runtime replay.
Use Node >=18, Java 17, the runtime's pinned Rust toolchain, and a C/C++ toolchain
for RocksDB. Dependencies and execution logs stay under `.work`.
Use GNU C++ 13 (`export CXX=g++-13`) for the pinned RocksDB 8.1.1 sources, matching
the Ubuntu 24.04 CI environment. GCC 15 exposes missing standard-header includes
in that upstream version. The runtime receipt records the selected C++ compiler
and flags; keep the same selection for setup, replay, and semantic controls.

Install the locked Quint dependency tree with `npm ci`, using a copy of
`state/package.json` and `state/package-lock.json` in `.work/quint`. Download
[Apalache 0.56.1, asset `apalache.tgz`](https://github.com/apalache-mc/apalache/releases/download/v0.56.1/apalache.tgz)
into `.work/quint-home/apalache-dist-0.56.1` (the archive contains `apalache/`).
Archive SHA-256: `91125e5a3646b9c9d3a7d921d3323f321fac5071909f72b3960c66ff2f998ee1`.
The adapter checks the JAR hash before executing TLC. Set `SHIELDD_PARI_KEYS`
to a complete compatible development registry. The real loader requires every
family; only one Transfer proof is generated for this pilot. Missing keys or
tools block replay, rather than replacing verified capabilities with mocks.

For a fresh local development registry, from the security repository root:

```sh
export CXX=g++-13
export SHIELDD_PARI_KEYS="$PWD/.work/pari-keys"
(cd .work/shieldd-current && cargo run --locked --profile ci -p shieldd-sdk-proof-params --example pari_setup -- "$SHIELDD_PARI_KEYS")
python security.py state
```

Setup refuses an existing destination and publishes only a complete registry.
The cache replay creates `.work/state/transfer.bin` on its first execution and
verifies those exact bytes again on every subsequent run.

Windows-mounted Node modules can load slowly in WSL. A temporary Linux copy may
be selected with `SHIELDD_QUINT_CLI` (CLI JavaScript path) and `SHIELDD_QUINT_HOME`
(checker cache). The selected CLI and JAR are checked against their pinned hashes.
Correct npm installation of the remaining
locked dependencies is a trusted toolchain boundary; the lock hash is an intended
dependency identity, not an independent audit of all installed module bytes.

The finite model explores ten transitions, heights 1–4, nondecreasing times
0–4, freeze epochs 0–2, two added assets, and grace windows 0/2. Neither time nor
epoch wraps. Bounds stop transitions; TLC deadlock checking is disabled because
these artificial terminal states do not represent runtime deadlock. The model
checks safety, not liveness. One worker uses at most 1.5 GiB JVM heap.

Root labels identify distinct authenticated roots, not field encodings. The
runtime fixture starts with real genesis, then registers one regulated asset
and user in block 1. Labels -1 name genesis roots and 0 name the registered
roots. Freeze labels encode generation and height; unfreeze retains generation.
This preserves root identity when a candidate is abandoned and reexecuted.
The driver binds labels to observed roots injectively and compares actual
pending and committed storage after every action, including pair/index records.
Registration admission, hash correctness, and cryptographic randomness remain
outside this abstraction.

Observation removes obsolete history in the finite model. With at most five
observations, the runtime deletion budget cannot bind. Monotonic observation
height/time and freeze epochs make obsolete entries a chronological prefix;
root renewal replaces its older observation. A separate runtime test retains
70 admissible equal-timestamp pairs and then checks the 64-deletion limit.

Quint exports deterministic traces covering paired roots, inclusive/expired and
zero grace, repeated timestamps, freeze/unfreeze, rollback, checkpoint checking,
and actual database shutdown/reopen. Its remembered proof token is abstract.
A separate runtime test warms the real byte/registry-bound cache with a genuine
Transfer proof, freezes an unrelated user, and delivers the same bytes through
`App::deliver_tx_bytes`. Freeze and unfreeze must both reject them without
transaction effects. Removing the actual epoch check must make that rejection
assertion fail; restoration must make it pass again. The mutation is applied
only in the disposable runtime checkout and restored byte-for-byte in `finally`.
Additional real-code controls must detect disjunctive root matching accepting a
mixed pair and skipped rollback restoration retaining an abandoned candidate.
Forced process-group termination can prevent `finally`; a dirty checkout then
blocks further evidence until the disposable source is restored to its exact pin.

These are a finite model check and implementation tests, not a Rust refinement
proof, whole-system certification, or Bankd settlement verification.
