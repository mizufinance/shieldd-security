# Snapshot and execution checks

The formal-owned `transfer_effect_controls.rs` and its exact
`transfer_effect_controls.patch` prepare five additional genuine full Transfer
tests at `844389ee069e1fb2e576708842d0b389b4d9a44a`. Their manifest
`transfer_effect_controls.json` binds each original file, patched text and named
test. This is a source-only candidate with no runtime result. Apply it only to a
fresh mutable diagnostic stage after verifying the base hashes; keep the clean
checkout and frozen observer stages intact. The child module reuses the existing
`family_fixtures` and `setup_test_txs` real witness/auth/proof builders and normal
delivery. It checks all spend slots, ordered outputs, ordinary volume payload and
day-scoped replay, FeeFunding without volume, and rollback after routing or index
staging in both index modes, retaining earlier accepted transaction effects.
The two transaction-ID-bound faults exist only under `cfg(test)` and do not
replace proof verification. Run the manifest's exact test names with a complete
matching `SHIELDD_PARI_KEYS` registry and `--test-threads=1`, under the current
single-heavy-job resource guard. Only an intended labelled failure with the
unchanged effect snapshot counts as a runtime control. Compilation failures and
offline resource checks do not qualify these tests or the Rust/Lean refinement.
The two admission tests reuse the actual body and fee proofs for typed claim
changes, exact rejection causes, capability-slot coverage and cache identity.
Changing a public claim also changes the expected statement, so rejection must
come from proof verification. Capability row permutation preserves slot binding;
swapping body and fee capabilities fails. A wrong registry lookup ID tests the
cache comparison; it does not test a separately generated same-family key set.

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

Each replay creates a new fixture attempt under the complete source, registry,
compiled test executable, enabled features and native-artifact identity. The
actual cache test builds and verifies the fresh proof before its transaction
bytes and positive producer log are bound in an exclusive sidecar. The older
shared `transfer.bin` is preserved and never reused. Mutations deliberately
consume this baseline fixture with explicit changed-source identities; they
alter only the named state-effect checks, not proof relations or keys. Restored
source, registry, fixture and sidecar bytes must match before a positive replay
can qualify the candidate. These identities accompany the actual proof and
layout checks; hashes alone do not establish those checks.

These are a finite model check and implementation tests, not a Rust refinement
proof, whole-system certification, or Bankd settlement verification.

`execution.qnt` adds a normative transaction-effect model: twelve transitions,
one transaction, committed heights 1–3, and separate pending/durable effects.
Its atomic application step is the required behavior, not a proof that Rust
implements atomicity. Valid proofs/action signatures and atomic storage batches
are explicit abstractions. The model checks safety, not liveness. Its seven
traces cover cold/cached execution, a committed-state CheckTx after pending
delivery, duplicate rejection, rollback, interrupted commit and database reopen.
The added traces check Idle and EndedBlock read-only admission, Idle rollback,
and CheckTx before and after the durable-write interruption boundary. CheckTx
must preserve both effect observations and the phase while using the durable
snapshot; after the write, it rejects the committed spend even while the
interrupted host still holds the old pending snapshot. A cold CheckTx after
reopen must populate the stateless cache despite rejecting a spent nullifier.
These additions are source-only until the exact updated model, traces and
runtime driver pass independent review and execution.

The Rust driver uses the existing genuine single-Transfer fixture through normal
HostExecution admission. It compares every spend nullifier, ordered output
commitments and payload bytes, exact transaction/index bytes, and pending and
durable state. On successful delivery it independently appends the proof-bound
commitments to the preceding SCT and checks the resulting positions and root.
Commit/recovery must preserve that full observation. Rejected operations return
no events or withdrawals and preserve the observed state; accepted delivery must
emit events. This does not yet prove the completeness of every event schema.

Test-only notifications pause the actual commit future after delta extraction
or immediately after the real atomic storage write. Cancellation after the latter
may recover the new durable state despite no successful response. Interrupted
host mutation entry points must reject until recovery. Reopening calls the real
database shutdown/load APIs; it is not an abrupt process or power-loss test.
An actual-runtime mutation omits SCT insertion while retaining payload execution;
the root assertion must reject it, and restored source must pass again.

This increment covers one ordinary Transfer and repeated delivery of identical
bytes. Distinct conflicting transactions, multi-action/fee combinations, Bankd
settlement, general storage failures and arbitrary crash recovery require their
own executed evidence. The new execution checks remain unqualified until the
full pinned command succeeds. Generic runtime proof tests explicitly exclude
the two external trace drivers; the combined security gate owns their inputs and
requires each named test to execute and pass. Missing traces remain errors.

## Execution correspondence

The source-only extension above targets runtime base
`90428db824c17a61a94cadede1a1a49602700b6b` plus the exact source bytes in its
diagnostic checkpoint. The checkpoint must be included in a newly verified
immutable runtime composition before replay; a base commit and subset hashes
alone do not establish the whole selected build. Earlier `bac25507` receipts
do not qualify these updated traces or the current 904 candidate.

| Model boundary | Actual implementation and observation |
| --- | --- |
| `check` | `HostExecution::check_tx` creates a separate App from `storage.latest_snapshot()`, selects `NoIndex`, and uses the shared byte/registry-bound stateless cache. It has no host mutation-phase guard. The replay compares both full effect observations before and after. |
| `deliver` | `HostExecution::deliver_tx` requires `InBlock`; ordinary decoded transaction admission resolves withdrawals and uses the actual transaction state delta. Successful execution applies that delta and defers transaction indexing. Rejection preserves both observed stores. |
| `cancelBefore` | `App::commit` flushes deferred indexing, replaces the pending app state with a delta over the old durable snapshot, and pauses at the test-only extraction notification before preparing/writing the batch. Dropping the future discards the extracted candidate; the host remains `CommitInterrupted`. |
| `cancelAfter` | The test-only persisted notification follows the actual `storage.commit_batch` return but precedes app snapshot reset. Durable effects/height advance while the host's pending delta still references the old durable snapshot. |
| `blocked` | Host mutation phase guards reject begin, deposit, compliance, seizure, delivery, end and commit after interruption. Read-only CheckTx remains permitted. |
| `rollback` | `HostExecution::rollback` constructs an App from the latest durable snapshot and resets to Idle, including when already Idle. It does not undo a durable write. |
| `reopen` | The replay consumes `HostExecution::release`, shuts down storage, loads the same database, and constructs a new host/cache. It observes durable nullifiers, payload bytes/positions, SCT root, transaction bytes and height. |

The model's effect booleans summarize this one fixture. Real roots, ordered
bytes and every fixture nullifier/output/index are checked by the replay, not
proved by those booleans. Storage batch atomicity, accepted proof/signature
semantics and cryptographic collision resistance remain explicit boundaries.
The two cancellation locations are controlled future interruption and orderly
database reopen; they do not establish abrupt process crash, power-loss,
consensus-network recovery or Bankd's independent record consistency.
