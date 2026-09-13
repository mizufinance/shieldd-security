# Required consumer security claims

These are required proof contracts, not completed reductions. Exact consumer
source identities and build obligations are owned by `decaf/obligations.json`.
Inspection pins do not attest to deployment or adoption of a candidate library.

## RDSA

Prove existential unforgeability under adaptive chosen-message attack for the
implemented signing and verification relation. State the hash/random-oracle
model, group hardness assumption, key generation distribution, nonce derivation,
domain separation and accepted encodings. Bind every input to the actual
transcript bytes. A vector match or valid-signature theorem is not unforgeability.

At inspection revision `504c04391d871bad8c667a475983696cd24d2cee`,
`src/signing_key.rs` and `src/verification_key.rs` expose SpendAuth key
randomization: `sk' = sk + randomizer` and `A' = A + randomizer * B`.
The game must cover the related-key signing/verification behavior selected by
consumers, identifying who chooses and learns each randomizer, allowed signing
queries, and the freshness relation for a winning key/message pair. An ordinary
single-key theorem alone does not cover this API. Prove the native randomized
key correspondence separately from its cryptographic reduction.

The same revision derives the signing nonce by hashing secret-key bytes,
48 bytes of bonus randomness, verification-key bytes and message bytes, in
that order. Deterministic signing sets all bonus bytes to zero. Its reduction
must cover both selected entry points and the actual hash domains; importing a
reduction that assumes an independently uniform signing nonce is insufficient.
Key generation reduces 64 random bytes modulo Fr, so bound the distribution
distance instead of assuming an exactly uniform scalar.

Verification accepts the identity as a key, and field-to-signing-key conversion
does not reject zero. The game must distinguish honest key generation from
adversary-supplied keys and state what security can be claimed for each consumer's
identity policy. Do not silently impose a nonzero precondition on these APIs.
Secret-derived points reach `vartime_compress` in signing, key derivation and
randomization; consumer adoption and compiled-trace obligations remain open for
these routes. Public verification routes need separate public-input arguments.
Under `std`, signing-key `Debug` implementations format the full secret-key
bytes. Inventory actual consumer formatting/logging call sites and their output
policy; the method's existence alone does not establish a reachable disclosure.

## FROST

Prove threshold unforgeability with up to threshold-minus-one statically corrupt
participants, adaptively selected messages and concurrently interleaved sessions.
Specify the signing oracle, participant/session binding, abort behavior and win
condition before claiming a reduction. Instantiate the implemented transcript,
binding factors, key validation and nonce distribution, including biased-reduction
bounds where applicable. Robustness and guaranteed service are separate claims.

Prove source transition refinement separately from this computational reduction.
The Orbis responder is one-use per successful insertion; the initiator is
one-use per successful local generation, not per request ID or scalar value.
The exact copy, cancellation, TTL, context, retry and crash obligations in
`nonce-contracts.md` remain binding. Inventory other FROST callers independently.

## Key agreement

Prove shared-secret correctness and CDH-based confidentiality for validated peer
points, with the implemented output derivation and hash assumptions stated.
Specify adversarial peer selection and prohibited secret-key disclosures.
Do not claim peer authentication or authenticated key exchange from bare group
agreement. Prove rejection/identity behavior against the actual API policy.

## Proxy re-encryption

Prove confidentiality and resistance to unauthorized transformation/collusion
for the actual construction. The source-closure proof must define the challenge
experiment, corruption and delegation graph, proxy/recipient collusions,
oracle queries, challenge restrictions and win condition. In particular, exclude
only disclosures that are authorized by the scheme, not attacks by definition.
The exact game remains an open source-binding obligation until these relations
are instantiated; the family name is not evidence that a game is defined.

## Shared boundaries

RNG entropy, independence, hash models and computational hardness must be named
in each reduction. Prove the implemented distribution or bound its deviation;
do not equate successful generation with fresh scalar bytes. Volatile crash
reasoning excludes restoring or forking process snapshots. Physical erasure and
operational availability are not established by these contracts.

CT is a separate relational property. Its public-state relation must permit
distinct secrets; equal public keys and functional key consistency must not
collapse the compared secret domain. Record declassification and output bounds.
