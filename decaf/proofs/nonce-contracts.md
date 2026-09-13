# Orbis nonce refinement contracts

Source inspection pin: `sourcenetwork/orbis-rs` at
`95bf179e8073f6decbe346a10984f23870c3d2d0`. These are source-reviewed contracts
for issue #6, not completed native refinements or deployment certification.
They do not establish nonce-scalar freshness or protocol unforgeability.

## Responder

The state manager is
[`response_state.rs`](https://github.com/sourcenetwork/orbis-rs/blob/95bf179e8073f6decbe346a10984f23870c3d2d0/bin/orbis-node/src/sign/v0/response_state.rs).

1. `store_nonce_for_version` (line 207) takes the write lock and sweeps expired
   entries before testing capacity, then duplicate keys. Successful insertion
   receives a fresh ghost insertion identity. Failed storage can still remove
   expired entries. It does not overwrite a live entry.
2. `consume_nonce_for_sign_request_for_version` (line 252) holds one write lock
   across lookup, peer comparison, and removal. Missing entries and wrong peers
   preserve the map. A matching peer detaches exactly one stored insertion.
3. `ConsumedNonce::into_bytes_for_context` (line 54) consumes the detached
   value. Exact context-key mismatch discards it; equality releases its bytes.
4. A detached insertion can terminate through rejection, cancellation, or at
   most one signing invocation. No transition reinserts that insertion.

The handler source is
[`coordinator/handlers.rs`](https://github.com/sourcenetwork/orbis-rs/blob/95bf179e8073f6decbe346a10984f23870c3d2d0/bin/orbis-node/src/sign/v0/coordinator/handlers.rs).
Round 1 generates typed state at line 444, serializes it by reference, and moves
the serialized bytes into storage. Track both that original typed object and
the serialized representation: serialization is not an ownership transfer.
Round 2 detaches the insertion at line 770, before message-size validation and
authorization awaits. It checks context and decodes the consumed bytes at line
898, then makes the signing call at line 918. The proof must bind that call to
the decoded stored representation and establish that the original Round 1
object is never signed in this handler.

One-use is per successful insertion, not per request ID or scalar bytes.
After removal, the same request ID can receive a new insertion while an earlier
detached handler is still in flight. Consume does not check TTL: an expired
entry remains consumable until a sweep removes it.

## Initiator

The separate local path is
[`rounds/nonce.rs`](https://github.com/sourcenetwork/orbis-rs/blob/95bf179e8073f6decbe346a10984f23870c3d2d0/bin/orbis-node/src/sign/v0/coordinator/rounds/nonce.rs)
and
[`rounds/signing.rs`](https://github.com/sourcenetwork/orbis-rs/blob/95bf179e8073f6decbe346a10984f23870c3d2d0/bin/orbis-node/src/sign/v0/coordinator/rounds/signing.rs).

Nonce generation at `nonce.rs:53` creates a local typed state, stored in an
`Option` at line 58 and moved to the caller at line 255. `signing.rs:764`
receives it. The serialization at lines 779–796 concerns public commitments;
the local secret state is neither serialized nor inserted into the responder
map. The sole local signing invocation is at line 821. Signing or verification
failure does not retry that invocation. Peer tasks at line 913 do not capture
the local secret state.

The required invariant is at most one signing invocation per local generation
event, including failed signing and later cancellation/network failure. A
successful local `generate_nonces` call receives a fresh ghost generation
identity, without assuming that the generated scalar bytes differ. Local state
remains owned across later awaits and is discarded when the attempt ends.
Response-map cleanup at line
230 executes after an await and can be skipped by cancellation; one-use must
not rely on that cleanup having occurred.

## Context and environment obligations

Context construction in `handlers.rs:457` must match line 887. Policy uses the
raw derivation ID, Bulletin includes the object ID, Report includes the report
ID, and RingReshareUpdate/RefreshHealthCheck use hashed constructions. Prove
these actual constructions and exact key equality. Do not infer typed-context
injectivity from string equality or from outdated field comments.

The library's
[`FrostSigningState`](https://github.com/sourcenetwork/orbis-rs/blob/95bf179e8073f6decbe346a10984f23870c3d2d0/crates/crypto/src/decaf377/sign.rs#L117)
has public fields, serializes by reference, and is borrowed by signing. Its API
does not itself enforce one-use. Both caller refinements therefore require
source control-flow and representation bindings, not just Rust ownership.

State-map atomicity depends on the actual lock/HashMap semantics. Crash
reasoning discards volatile map and detached/local states and excludes restored
or forked snapshots. RNG freshness, hash/protocol assumptions, compiler/runtime
correspondence, cancellation semantics, and physical-memory erasure remain
separate explicit obligations. No durable nonce store is assumed.
