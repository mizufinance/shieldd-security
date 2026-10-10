# Native statement, role and recovery source review

These read-only parent reviews record exact pinned runtime/formal source
identities and capture role-link data. They add no Lean replay, runtime test
or certification result.

The native typed statement order agrees with the formal structured 64-field
sequence. Captured source witness ordinals map through the original-input
offset to stored columns: public source22734 maps to22737, committed source6
to9; rows200767/200768 link these to verifier columns1/2. Row200769 links
constant-zero slot0 to the outlined-one copy200692.

Transaction delivery uses an exclusive child delta and applies it after
effects/indexing succeed. Deferred flush takes its queue before fallible
index writes, so an error is not an automatic queue restoration. FFI panic
handling does not rebuild the service. Explicit rollback recovers the latest
durable boundary and reconstructs App. A commit error can occur after durable
application persistence, so recovery cannot always be described as old state.

Concrete SDK/hash/codec instantiation, full row-to-TransferSem, exact native
Transfer effects, abort/recovery transitions and supporting native fault tests
remain owned obligations. Full Transfer remains OPEN.
