# Transfer state correspondence work

This work targets runtime commit `844389ee069e1fb2e576708842d0b389b4d9a44a`.
The four handwritten models below passed their narrow Windows kernel checks:
StateDelta3020 (12 theorem audits), staging3027 (16), public call3053 (10), and
ordered reader3056 (6). Exact receipts are recorded in `EXECUTION_PROGRESS.md`.
They do not establish a universal Rust refinement or durable recovery result.

`TransferStateDelta` models the three normal child-cache write channels,
newer-write precedence, cache-stack order, events, and delivery indexing.
`TransferNullifierStaging` models the normal nullifier helper's checks and
ordered append. `TransferNullifierPublicCall` models its public wrapper.
`TransferNullifierReadVector` models the reader's ordered result collection;
its six checked theorem audits derive exact length and pointwise association
for success and propagate errors without partial vectors. The per-nullifier
callback denotes the status/verify/return block at one captured boundary;
authenticating that callback and proving Rust correspondence remain obligations.
All four models have finite heartbeats and use symbolic list operations.
They do not expand the full Transfer constraint matrix.

| Model operation | Pinned source | Correspondence obligation |
| --- | --- | --- |
| Merge child writes and apply to the original parent | `third_party/cnidarium-0.83.0/src/cache.rs`, `src/delta.rs` | Establish map overwrite, deletion, event order and typed object behavior for normal transaction caches. Maintenance range deletion is outside this model. |
| Preserve the parent on a failed delivery | `crates/core/app/src/app/delivery.rs:165` | Relate exclusive `try_begin_transaction`, child ownership, every `?` return before `apply`, and the delayed deferred-queue append to the functional result. A functional `finish` theorem alone is insufficient. |
| Check registry before constructing the child | `crates/core/app/src/stateless_cache.rs`, `app/delivery.rs:169` | Relate the real registry identity and privately minted artifact to the admission model. Equality of an arbitrary Boolean is insufficient. |
| Validate and append nullifiers | `crates/core/component/sct/src/component/tree.rs:62` | Relate local `BTreeSet` uniqueness, `PendingNullifierBlock::Open`, saturating length check, pending membership, durable read, and the single final `object_put` to `stage`. |
| Return a complete authenticated durable-read vector | `crates/core/component/sct/src/permanent_nullifiers/store.rs:40` | Relate the successful `map`/`collect<Result<Vec<bool>>>` to one Boolean per input in input order. Each Boolean is returned only after `status.verify` succeeds against the read boundary. Authenticate the status under the explicit tree/hash assumptions. |
| Include pending spentness in reads | `crates/core/component/sct/src/component/tree.rs:522` | Relate the reader vector and pointwise pending-membership OR. A truncated vector must never satisfy the relation. |

The nullifier model preserves the check order and distinguishes reader failure
from an unspent result. Its length check explicitly uses `min size usizeMax`;
the checked saturation lemma requires `32768 < usizeMax`. This holds for the
supported machine word sizes but must be included in the platform relation.
The ordered result includes every supplied slot, including dummy nullifiers.

The staging model describes `stage_nullifiers`. The additional
`TransferNullifierPublicCall` models `nullify_all`'s immediate empty-input
return, transaction source-ID check and enabled durable check. Its two-call
consequence preserves body nullifiers while appending both fee nullifiers;
every serialized slot is retained, including private padding. It has ten
checked finite-heartbeat theorem audits. Decoding the
actual body and fee input lists and relating the Rust calls remain source joins.

The runtime's pending container uses `imbl::Vector` and `imbl::OrdSet`.
`StateRead::object_get` produces a typed cloned value, which the helper mutates
before its final child-cache write. A refinement must establish the persistent
containers' clone and mutation behavior; it cannot infer deep-copy semantics
merely from `#[derive(Clone)]`. The durable reader is a shared capability and
is read by staging, not replaced with a disposable copy of the database.

Source inspection confirms that `try_begin_transaction` uses `Arc::get_mut`
and constructs a new delta over a unique mutable parent reference. Object reads
search the leaf cache, then layers from newest to oldest, then the parent; a
cached deletion stops the search. The returned value is a typed clone.
`object_put` writes a new boxed value into the child leaf cache and checks the
existing object type. Normal cache application moves the object boxes and
returns the separately collected events. These are source observations, not
a Rust refinement theorem. In particular, `Clone` permits shared interior
mutability for arbitrary object types, so the immutable-object model must be
related to each concrete Transfer-touched type rather than every possible
`StateRead` object. The pending nullifier containers and shared durable reader
have different roles in that obligation.

The six prepared genuine Transfer tests in `state/transfer_effect_controls.rs`
remain uncompiled and unrun. They use the existing full-relation MockClient
fixtures and matching Pari registry, verify real body and fee proof slots,
check the listed effect queues, spentness, volume markers, SCT position and
transaction indexes, and inject transaction-bound errors after
routing or indexing. The test overlay applies cleanly to the exact clean pin
under `git apply --check`; that is a source check only. A compiler error, missing
registry, timeout, fixture failure or wrong error cause receives no control
credit. Complete matching setup, actual test execution, committed readback and
recovery checks remain required.

A fresh native suite has now been queued after the serial Windows proof checks.
Its source archive comes from the exact clean runtime commit, includes the
current six-test overlay and retains the original circuit sources. It uses
separate stage, target and development-key directories. It must build the
setup program, generate all seven matching key families, build the native app,
verify the exact test inventory, and run each of the six named tests separately.
Source and key inventories are checked before and after execution. Finite time,
memory, disk and owned-process guards stop the suite on failure; compiler errors
and missing resources remain failed attempts. This suite is currently waiting,
with no new Cargo, setup or runtime-test result. The earlier three-test stage
and its source receipts are retained separately.

Nineteen existing pinned SCT and permanent-nullifier tests are queued after
that genuine-proof suite. They cover reference spentness, stale and duplicate
updates, authenticated presence despite an index miss, partial commits, recovery
selected by the application boundary, missing data, independent trie roots,
immutable exports, codecs, live anchors, sealing and SCT reload. The WAL/meta
parent checks both intended crash exits are exactly 77 before reopening and
checking spentness; its standalone worker returns without doing work when the
crash environment is absent and is therefore excluded from the test inventory.
This is still a waiting runtime suite, not completed recovery evidence or a
universal filesystem/refinement proof.

A separate same-relation, different-key control is prepared in
`state/transfer_cross_key_controls.rs` and queued after those recovery tests.
It requires the production loader to accept two complete, independently
generated development registries with the same Transfer relation and different
Transfer verifying keys. Genuine body and fee proof occurrences must pass under
the first key and produce `invalid Pari proof` or `invalid Pari proof batch`
under the second. Wrong family, wrong relation, malformed keys, missing fixtures,
and compiler errors cannot satisfy this control. It also checks that capabilities,
verified transaction artifacts and exact-byte cache entries remain scoped to the
actual first registry. Fresh source, target and second-key directories preserve
the earlier source snapshots and binaries. This remains a source-only control
awaiting native execution; no cryptographic rejection has yet been observed.

Review of the concrete SCT object adds a further observation requirement.
Its tree stores an `Arc` to the frontier and uses `Arc::make_mut` before the
insertion path writes the child tree cache. That source pattern must still be
related to the cache model. The original six-test snapshot records the SCT
position and omits its root. A fresh successor overlay adds a copied `tct::Root`
from the fallible `try_get_sct` read to every effect snapshot, so each rollback
comparison also checks the root observed before the failure. It preserves the
original source snapshots and uses a fresh source/build directory with the same
matching first registry. This replay is queued after the initial-witness check;
its six test names repeat the earlier controls and do not count as six additional
independent controls. It remains uncompiled and unrun.
