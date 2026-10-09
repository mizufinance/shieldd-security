# Orbis protocol design for independent review

Current target (2026-10-01): Shieldd PR160 is pinned to
`844389ee069e1fb2e576708842d0b389b4d9a44a` in `shieldd.lock`. The clean
checkout identifies the current runtime source; it is not a certification.
The canonical PRE/signing/test input identities are frozen in the reviewed
`aa767adc...` source packet. Its nine handwritten `OrbisPreAlgebra` equations
are source-approved and unrun. They establish no secrecy or runtime caller
correspondence; the separate native/module dependency and execution gates remain
open. A standard co-CDH reduction with the proposed AGM/ROM treatment,
joint hash-to-curve/SHA assumptions, HKDF/AEAD composition, online reader-PoP
extraction, caller refinement and finalized ACP authorization are still open
obligations. M2–M4 remain open.

The sections below are historical protocol contracts and dirty Orbis service
diagnostics. Their “current” candidate/checkpoint wording describes those
recorded snapshots, including `90428db...`, and does not identify PR160's current
runtime or qualify its PRE/caller implementation. Preserve each old source,
result and limitation as historical evidence.

Status: protocol contract and scoped service diagnostics, not a security
certificate. Production enablement stays disabled. The actual source map and
deployment mismatch are in [bankd.md](bankd.md). Runtime source is the current
`90428db824c17a61a94cadede1a1a49602700b6b` candidate with uncommitted assurance
changes; this document does not certify that tree.

Current execution checkpoint: the reviewed dirty Orbis source `9f8339f5…`
passed four origin-outbox tests, two durable round-journal tests, and the
targeted Tamarin local causal-order lemma on model `96778ccb…`. These are
diagnostic results, with exact identities and logs in the ignored receipts.
They do not qualify the newer retirement changes, live secrecy, STORM or
production enablement. The corrected five-process public-fixture run on source
`b6e4cfb5…` passed all six honest, equivocation, partial-delivery and restart
scenarios in 69.58 seconds, with independent result review. Its test-only KDF
profile allowed postcommit replay within the unchanged five-second schedule;
late restart was explicitly refused. The original deadline refusal remains
recorded. This does not establish production KDF startup latency or physical
synchrony. On exact dirty source
`75bf1c174af9e15cb01b27e0ad102db12e837fd7071f7e28250c81f36cefd49c`,
the three actual Redb retirement tests and four origin-outbox tests passed,
with all required marker counts, source/binary/lock postchecks and owned cleanup.
The node `--lib` build failed with nine internal method-visibility errors and
two stale test assertions against `Result<bool, DkgError>`; no node retirement,
expiration or publication test ran. The independently reviewed three-file repair
changes only `session_state` helper visibility to `pub(super)` and unwraps those
two Results with failure-producing expectations. Exact derived dirty source
`ea353c681ffa7f66659167303a4b3694f90689d3f1f9e5a18b77466a92ecaa9b`
compiled the node library and passed the one retirement-manager and one
expiration-worker test. Its publication group passed three tests and failed
`origin_submit_rechecks_context_after_durable_reservation` with
`SessionNotFound("4274")`; the required `ORBIS_OUTBOX_RACE` marker was absent.
This is a semantic test failure, not a successful refusal control. The generic
signature verifier's session lookup obscures terminal lifecycle status before
the typed recheck. A separate frozen one-file candidate adds a lifecycle recheck
before that lookup, retaining every existing guard and test assertion. Exact
derived dirty source
`f1f18ea2542e2077ce0d9cad1f219c26a36cec749429507f04abfea63cb47243`
compiled the node library and passed all four publication tests, with exactly
one `ORBIS_OUTBOX_SUBMIT` and one `ORBIS_OUTBOX_RACE` marker. The test binary was
`d3c67016b3da97fc94f566ea75de95266229e7854d0fdeb48e6e3c76e09b2f3d`.
Compilation took 102.1838 seconds. The actual tests took 5.12 seconds;
the supervised replay took 6.3776 seconds.
Source, binary, lock, runner and monitor postchecks passed and owned cleanup
was confirmed. The new receipt and log remain in
`.work/diagnostics/orbis-publication-f1f18-node-20260930-01`; the log SHA256 is
`409d2a73563cf0b1ca04d724a58ce0fc06e67d0b0d9ad8e88532b3610ff542f1`.
Independent actual-result review approved these four historical tests; the
immutable review index is
`.work/diagnostics/orbis-publication-actual-result-review-20260930.json`
(`16530e0b22817b6d3382bb3195f34b13d3cc109eb9048e012b88ad43587c3979`).
The shared binary path subsequently contains the separate `f1186f1a…` PRE
build; the compiler and test receipts bind the historical `d3c67016…` bytes,
which must not be imported or executed through that overwritten path.
This qualifies the selected reservation-change scenarios and exact persisted
message replay. Remote leader request/ACK and offline-loop behavior, deadline
abandonment, stale retry tasks, and the final-check-to-dispatch window remain
unqualified. The leader-change and expiry cases have no executed guard-omission
controls. It does not establish every lifecycle race or the separate PRE expiry
candidate.
The earlier failed receipts remain in
`.work/diagnostics/orbis-visibility-ea353-node-20260929-01`.
The 75bf storage receipts qualify only their selected storage source/binary.
Neither result establishes live secrecy or production release, and STORM stays
on hold.

The PRE local-handoff expiry correction is a separate source candidate. It
preserves the existing 300-second clock-skew contract and rechecks all token
time claims after constructing the actual signed share or collected response,
immediately before local return. Authored genuine handler/service controls
advance an isolated test clock during ACP and after actual signing/collection;
they require denial at the existing `exp + 300` skew boundary and successful
real crypto one second before it. On exact dirty source
`8272636930570fe71e6b3d6432f342a5fa283dec713cd0f95dd6d93362cb7c78`,
node binary
`f1186f1ad12a5721d8d2536495c70ae0a672f3075444b11f8a822f02c1edd109`
passed both named responder/service tests, with one required marker each.
The supervised tests took 4.3634 and 4.3743 seconds, respectively; source,
binary, lock, runner, monitor and cleanup checks passed. Exact receipts remain
in `.work/diagnostics/orbis-pre-827263-20260930-01`; responder and service log
SHA256 values are `456deb3e866817f88b8a5603bcac5a7e26f86c105c3a241cbe2a51d79201dbbe`
and `c05ec1759d00fd5107c2e94cae2176d289ee6a339750cea205632fd367aaf184`.
Independent actual-result review approved this scope. Each test exercises a
single real BLS share with dummy ACP and a task-local clock. Service positive
cases decrypt the expected plaintext; responder cases assert nonempty signed
fields, without independently verifying the response signature. The guard-
omission semantic mutant has not been executed. A late refusal can leave the JTI
consumed and remote shares collected; `signed_at` and request `created_at` can
precede the handoff check. This does not assert physical network-delivery time,
threshold-corruption secrecy or authenticated finalized-policy freshness.

The implementation targets two separate operations. Public capsule disclosure
opens an exact accepted capsule under an explicit authority grant, even if a
claimed owner later fails the seizure proof. Ownership PET answers an authorized
equality query about an accepted Transfer ownership ciphertext. Transfer's
ownership ciphertexts do not cover every capsule. Neither operation is a
substitute for BLS PRE delivery of opaque openings to a private reader.

## Specialist review and production dependency decision

This is a review package for a still-open implementation choice, not a selection
of the experimental STORM/DS code as production architecture. The inspected
service base is `sourcenetwork/orbis-rs@0a0f935a85cc60e87561a9c7364fa80fdb3332df`;
the Shieldd candidate starts at
`90428db824c17a61a94cadede1a1a49602700b6b`, and the inspected Bankd consumer at
`d85ef61a29383894d18014b4dc2ae2ebfa67a026`. Local qualification changes are dirty
and require new exact commits and combined evidence before certification.

The proposed composition to review is STORM Fig. 11 encryption-key generation
in the exact Jubjub prime subgroup, the committed-blinding JJ00 PET below, and
registered-share verifiable decryption of an exact accepted Shieldd capsule.
The fixed experiment has five participants, reconstruction threshold two and
one Byzantine participant. It preserves the full ordered NIKE factor set and
recovers missing dealers' **alpha**, not beta. It is a weakly robust protocol;
round-one failure may abort. Neither the source implementation nor finite
vectors establish its computational security or its composition with PET.

Questions requiring a cryptographic specialist's written disposition:

- Does the exact scalar/point codec, independent role keys, H2/H1 transcript and
  SHA-512 wide-reduction suite instantiate the cited security game, including
  bias, domain separation and selective-abort behavior? Whole-field sampling
  includes identities; activation that rejects zero public shares or keys needs
  explicit conditioning analysis, not silent resampling.
- Do the selected corruption model, threshold, authenticated broadcast rounds,
  missing-message rules and recovery evidence satisfy both constructions? The
  current artifacts do not establish adaptive security, erasure, refresh or
  reshare composition. Fixed-profile DS process tests do not prove deployment
  clock/network bounds or a dynamic-membership broadcast protocol.
- Does PET/release evidence bind the exact accepted ciphertext, registered
  public shares, roster/epoch, operation and authority grant? Deterministic
  partial decryptions accumulate across request IDs; transcript labels cannot
  manufacture independent secrecy domains. Public disclosure and private-reader
  BLS PRE must have separate confidentiality conclusions.
- Which maintained implementation and audit boundary should own this protocol?
  Any retained local cryptography needs named maintenance and independent
  composition review; unused qualification alternatives should be retired.

Primary reuse assessment, checked during this campaign: maintained
[FROST](https://github.com/ZcashFoundation/frost) and
[RedDSA](https://github.com/ZcashFoundation/reddsa) concern threshold signing;
their existence does not qualify this encryption DKG/PET composition.
[Ferveo's original repository](https://github.com/anoma/ferveo) warns about audit
and readiness, and the [NuCypher fork](https://raw.githubusercontent.com/nucypher/ferveo/main/README.md)
reports inactive maintenance. [Shutter's encryption implementation](https://github.com/shutter-network/shutter/blob/main/shlib/shcrypto/encryption.go)
uses pairing-based BLS machinery, requiring a deliberate cryptographic/wire
migration for this Jubjub consumer. These observations do not establish that no
compatible maintained implementation exists. The [STORM paper](https://eprint.iacr.org/2023/292.pdf)
is a protocol reference, not an implementation assurance artifact.

Available review assets are the actual BLS PRE lifecycle model and handler
tests, tested encrypted outbox and fixed-profile process journal, the disabled
Jubjub evidence verifier, and the optional STORM arithmetic core with independent
integer-vector checker. The latter core and new secret-record CAS are authored
qualification assets, not executed service evidence; their exact hashes belong
in a reviewed execution receipt after compilation. The current-record CAS is
default-off and has no node consumer. It does not establish send ordering or
validate an arbitrary caller's protocol record. No new service endpoint or
registry activation is authorized by these assets.

The smallest external-owner input is a concrete choice of maintained protocol
implementation/suite and its supported security profile, plus the authoritative
registry/activation contract. Current Orbis `RingPayload.ring_pk` belongs to the
BLS path and must not be overwritten with Jubjub material. No accepted
governance-controlled Jubjub roster/epoch activation adapter has been identified.
Likewise, current Vera ACP returns a local authorization decision; client timing
around that call does not authenticate a finalized policy revision or bounded
backend freshness. Deployment owners must identify the actual consistency and
schedule contract before a stronger claim is made. Specialist review, actual
owner adapters, exact artifact/deployment pins and adversarial service replay
remain release gates. No reviewer has been contacted or paid through this task.

## Qualification constructions and assumptions

The qualification candidate uses the committed-blinding PET and verifiable ElGamal partial decryption in
[Jakobsson–Juels, Mix and Match, 2000, section 2](https://www.arijuels.com/wp-content/uploads/2013/09/JJ00a.pdf).
Retain its commitment round. The cited malicious-security argument assumes
static active corruption below half the participating servers, authenticated
broadcast, DDH for privacy and discrete-log hardness for robustness; applying
Fiat–Shamir adds the random-oracle assumption. A generic threshold setting does
not by itself establish those conditions.

The encryption-key generation qualification candidate is the published STORM construction in
[Komlo–Goldberg–Stebila, 2023/292, figure 11 and section 6](https://eprint.iacr.org/2023/292.pdf),
including its mandatory accept/fail round and recovery of missing final
openings. It is a synchronous, honest-majority, weakly robust construction in
the CDH/random-oracle setting. Weak robustness permits abort: it is not a
guaranteed-termination service. The local FROST DKG is not an implementation of
STORM, and a FROST signing-security argument is not an encryption-DKG proof.

Let `n` be the registered participant count, `k` the reconstruction threshold,
and `f` the declared maximum corrupted participants. Require `f < k`,
`k <= n-f`, and `2*f < n`. Start qualification with `(n,k,f)=(5,2,1)`, which
also avoids relying on an expansion of the PET paper's threshold notation.
This is a local qualification profile, not an assumed production configuration.
Other profiles require an explicit checked security-parameter mapping. No
adaptive corruption, proactive refresh, resharing, side-channel resistance or
post-quantum guarantee follows from this proposal.

The papers establish constructions under their models, not this composition's
Jubjub implementation. Computational composition review must cover the exact
DKG, PET, proof transcripts, authorization oracle and permitted queries before
enablement. Tamarin will model the implemented messages and state transitions;
an ideal `PET` or `Authorized` fact cannot discharge these obligations.

## Jubjub types and key registry

Use `shieldd_sdk_crypto::{Fr, SubgroupPoint}` for subgroup scalars and points.
Do not use `Fq`/Pari's field for Shamir arithmetic. Use the deployed SpendAuth
generator `G`; the distinct deployed Sapling Binding generator is the proposed
Pedersen base `H`. Its unknown-log relation to `G` is a cryptographic setup
assumption, not something established by checking point inequality. Review and
pin both generators and their upstream derivation before using `H` here.

Canonical encodings, subgroup validation and role keys follow the actual
`docs/jubjub-external-contract.md`. External public keys and capsule EPKs must
be nonidentity. Internal PET differences, individual zero blinding shares and
polynomial coefficient commitments may legitimately be identity: do not
reuse a decoder that rejects every identity point indiscriminately.

One authenticated registry record contains protocol/suite version, chain,
ring, key role, epoch, `n/k/f`, sorted nonzero distinct field identifiers,
participant authentication keys, aggregate polynomial commitments, public
verification shares, aggregate key, DKG transcript digest and activation state.
Its authorization comes from the actual asset/ring governance path, not a
coordinator-supplied list. Separate ceremonies generate payload, checking and
RNK keys; wallet signing keys are never imported as encryption shares.

For aggregate coefficient commitments `A[0..k-1]`, check
`K=A[0]` and `Y_i=sum_j i^j A[j]`. A participant verifies its stored secret
share `x_i` by `x_i G=Y_i`. Check the full registry on load and bind its canonical
digest into every operation. These equations establish consistency, not DKG
secrecy or unbiased generation. Reject a zero aggregate public key and every
identity participant verification share `Y_i`: an identity share means the
corresponding secret share is publicly known to be zero and reduces the
effective secrecy threshold. Do not count it as an unexposed secret share.
For the initial degree-one profile, also reject an identity linear coefficient
commitment: a constant polynomial makes every individual share a decryption key.
The qualification profile aborts that ceremony before activation; its restart
rule and conditioning require computational review. Under an honestly uniform
degree-one polynomial, each such event has probability `1/|Fr|`, so a union
bound covers the aggregate key, linear coefficient and five shares. Applying
that argument to the
actual malicious-party DKG, including selective aborts, is a separate obligation.

STORM implementation must preserve figure 11's rounds: broadcast NIKE/VSS
commitments and privately send shares; validate and broadcast accept/fail;
only then reveal the second NIKE secret; recover incorrect/missing openings
as specified, then aggregate. In additive notation its final tweak gives
`x_i=v+sum_j w_ji`, `A[0]=vG+sum_j D_j[0]`, and
`A[l]=sum_j D_j[l]` for `l>0`. All ordered vectors and domain-separated hash
inputs must be canonical. No final-round participant may be silently dropped
to produce a different key. The exact paper algorithm remains normative;
these equations are not a replacement implementation specification.

The present upstream mesh is not an identified implementation of the paper's
authenticated reliable broadcast or round agreement. This is a blocked DKG
integration prerequisite. For the first disabled local verifier slice, a
fixed-roster certificate may contain every participant's signature over one
canonical round digest, with durable single-digest locks at honest signers.
This establishes agreement for accepted certificates; withholding can prevent
any certificate. It is not reliable broadcast and cannot silently replace
STORM's communication assumptions. In particular, requiring fresh unanimous
acknowledgments after key disclosure can enable selective abort: STORM's recovery
of missing final openings must not be replaced by discard-and-restart. A real
broadcast/ordering adapter and its round/fault mapping need independent review
before implementing or activating the DKG service. No such adapter is claimed
to exist in the current Orbis deployment.

Existing RedJubjub field/group operations, codecs and VSS helpers are reuse
candidates. The selected DKG's round machine, transcript and recovery logic
are new work. The [ZF FROST audit scope](https://github.com/ZcashFoundation/frost)
and [RedDSA's ZIP 312 FROST integration](https://github.com/ZcashFoundation/reddsa)
must not be described as an audit of Jubjub PET or this service.

## Exact PET relation and rounds

For accepted ownership ciphertext `(R,C)`, checking key `K=xG`, and validated
address fingerprint `M`, form `U=R`, `V=C-M`. Derive `M` with the deployed
fingerprint routine; do not introduce an alternative hash-to-curve mapping.
The request binds the accepted transaction/action/ownership slot and address.

Fix the full registered PET participant set before round one. Participant `i`
samples independent `z_i,r_i` in `Fr`, broadcasts `B_i=z_i G+r_i H`, then,
after all commitments are fixed, broadcasts `U_i=z_i U`, `V_i=z_i V`.
It proves knowledge of the same `z_i,r_i`: for fresh `a_i,b_i`, publish
`T1=a_i G+b_i H`, `T2=a_i U`, `T3=a_i V`; challenge `c` hashes the complete
session/round statement; respond `s=a_i+c z_i`, `t=b_i+c r_i`. Verify
`sG+tH=T1+cB_i`, `sU=T2+cU_i`, `sV=T3+cV_i`.

After all proofs pass, set `U*=sum U_i`, `V*=sum V_i`; obtain verified threshold
decryption `D=xU*` and return only whether `V*-D` is identity. Do not return
`C-xR`. If `U*` is identity, abort this attempt; never interpret degeneracy as
equality. This explicit negligible-event rejection and the Fiat–Shamir
instantiation are adaptation points for composition review.

A missing/invalid PET message aborts the entire fixed-set attempt. Do not
salvage a chosen subset of already revealed blindings. Restart uses fresh
randomness and a new attempt ID linked to the same authorization; rate limits
and expiry still apply. This initial service trades availability for a simple
fail-closed contract. No malicious-quorum liveness claim is made.

## Versioned partial-decryption evidence

Introduce a distinct threshold wire variant; do not reinterpret the existing
single-key `CapsuleReleaseEvidence` as threshold evidence. The new envelope
contains version/suite, operation, exact request ID, grant digest, registry and
DKG digests, key role/epoch, accepted block/transaction/action/field locator,
ciphertext digest, output mode, recipient binding and session/attempt digest.
Public seizure mode uses an explicit `PublicDisclosure` recipient tag. Private
reader mode is unsupported here and must reject, not emit the same plaintext
evidence with a reader label. Existing BLS PRE remains its own protocol.

For capsule EPK `E`, participant `i` emits `D_i=x_i E` with a fresh-nonce
Chaum–Pedersen proof. For fresh nonzero nonce `u`, commitments are `A=uG`, `B=uE`, response
`s=u+c x_i`; verify `sG=A+cY_i` and `sE=B+cD_i`. The challenge includes the
entire versioned envelope, participant ID and canonical `G,Y_i,E,D_i,A,B`.
Reject identity proof commitments: a zero nonce would expose `x_i` through
`s=c x_i`. This check does not establish nonce unpredictability or non-reuse.
Use a new domain-separated Blake2b-512-to-`Fr` transcript, distinct from issuer,
single-key capsule and PET proofs, with the byte contract below.
[RFC 9497 section 2.2](https://datatracker.ietf.org/doc/html/rfc9497#section-2.2)
is a DLEQ engineering reference; Jubjub is not one of its defined suites.

For a canonical set `S` of at least `k` distinct registered participants, check
every proof and calculate `lambda_i=product_{j in S,j!=i} j/(j-i)` in `Fr`.
Require `sum lambda_i Y_i=K` and combine `D=sum lambda_i D_i`. The consumer
checks every binding again against its expected request and registry. A bad
share is an error, not silently ignored input. Never sum independent DLEQ
responses to pretend they form the old single proof. Consistent aggregation
does not itself prove authorization or confidentiality of the now-public `D`.

## Canonical transcript byte contract

For this proposed version, use fixed-width `u16/u32/u64` little-endian integers,
canonical 32-byte Jubjub scalars/points, and byte strings prefixed by `u32`
length. Participant identifiers are nonzero `u16` values mapped injectively to
`Fr`; vectors are length-prefixed and sorted by identifier, with duplicates
rejected. Reuse the runtime's existing text/chain bounds. Bound the prototype
registry to the five-participant qualification profile; do not accept arbitrary
roster sizes without a resource and parameter review.

Define `Context` as the preceding envelope without proofs, responses or its
own digest. Its fields have the listed fixed schema order; the wire decoder
must reject unknown fields, duplicate singular fields and noncanonical
re-encodings. `context_id = Blake2b-256(domain_context || encode(Context))`.
Include the complete canonical existing release request and its existing
`release_id`, not only an unverified claimed digest. The authorization grant
signs this context ID excluding the grant's own signature/digest; the final
operation context then adds the canonical signed-grant digest. This explicit
two-stage binding avoids a self-referential grant hash.

An attempt ID is 32 fresh random bytes reserved durably. It is not a new
authorization and does not reset exposure accounting. A capsule share challenge
is `Fr::from_bytes_wide(Blake2b-512(T))`, where `T` is, in order:
`LP("shieldd.orbis.capsule-share.v1") || suite:u8 || context_id:32 ||
registry_digest:32 || attempt_id:32 || participant_id:u16 || G:32 || Y_i:32 || E:32 || D_i:32 ||
A:32 || B:32`. The response scalar is canonical; never reduce attacker-provided
scalar encodings on decode. An authenticated participant message signs the
context, attempt, round, participant ID and complete canonical response bytes.

PET's challenge uses distinct domain `shieldd.orbis.pet-consistency.v1`, the
same context/attempt/participant prefix, canonical digest of the complete
ordered commitment list, digest of the complete ordered blinded-pair list,
then `G,H,U,V,B_i,U_i,V_i,T1,T2,T3`, each as 32 bytes. All participants agree
on both list digests before accepting a proof. The subsequent decryption uses
domain `shieldd.orbis.pet-decryption.v1` and binds the verified consistency
transcript and `U*,V*`. Cross-operation proofs must fail even when points match.
STORM's `H1/H2` get separate protocol/role/epoch domain prefixes and canonical
ordered inputs exactly matching its construction, never these proof domains.
The hash instantiation and all these contextual extensions are explicit
computational-review targets; a domain string is not a security proof.

## Authorization and revocation contract

The existing seizure instruction signs note/nullifier/address/asset/value,
freeze generation/height, withdrawal destination and expiry. The existing
release request additionally binds capsule, keys and Orbis policy, but a
request is not a grant. Define an explicit signed disclosure grant over the
new envelope and the existing instruction commitment. Resolve its signer from
the authenticated asset seizure-authority policy. A generic PRE JWT or a
post-opening Pari owner proof cannot substitute for this grant.

Before any share operation each participant must independently validate:
canonical request and grant signature; accepted-note/capsule membership and
exact payload bytes at a verified finalized state; instruction/request/key/
epoch/policy agreement; relevant current freeze and authority status; expiry;
and its own membership and operation permission. A claimant's RPC response is
not finalized-state evidence. Reuse the actual Bankd/Comet verified state path,
or explicitly identify and qualify an authenticated trusted-state adapter.
Public opening is permitted independently of later claimed-owner success;
PET is not an invented precondition for every capsule.

Preserve per-participant fresh authorization and existing expiry semantics;
do not add an irreversible permit. Each honest participant linearizes its own
decision at a verified, monotonic authorization view immediately before the
durable emission commit. It rejects revoked/expired grants at that view. The
adapter must enforce a configured maximum view age against a verified chain
head, including its chain identity and finality rule; failure to establish
freshness denies emission. Production activation must pin the actual age
bound and adapter. No unconfigured or infinite default is permitted.

This is bounded freshness, not instantaneous global revocation. A revocation
outside a participant's permitted view can race its emission. State the exact
height/time bound and chain-progress assumptions in the model and test. A
later revocation cannot retract an already issued share, and an emission does
not promise that later seizure settlement will remain valid. Retry emission,
including a cached response, must recheck current authorization and expiry.

Partial decryption is deterministic: `D_i=x_i E` does not contain the request
ID. Binding a DLEQ challenge to a request does not prevent an adversary from
combining previously disclosed points for the same key/EPK from different
requests, grants or participant subsets. Model cumulative exposure indexed by
the actual key epoch, participant and EPK, not ideal request-tagged secrets.
Count a durable emitted response as exposed even if its network delivery is
uncertain. Confidentiality ends when accumulated exposed or compromised shares
permit reconstruction; there is no fresh confidentiality budget per request.

Likewise, reused EPKs under the same payload key share the same opening point
across capsules. Exact grant checks cannot create cryptographic isolation that
the ciphertext lacks. Audit nonce-generation/freshness assumptions and test
this exposure explicitly; the present runtime does not acquire a new consensus
EPK-uniqueness rule merely because the service has a request ID. PET blinding
attempts also require fresh independent randomness and cumulative-exposure
analysis. A stronger policy would require an explicit protocol/product change.

## Durable participant state and replay

For the proposed service, key durable state by `(registry, operation, request,
grant, participant, attempt)` and bind token identity to that exact digest.
Authenticate and validate public input before reserving a token. Atomically
reserve `(issuer,JTI)` plus the operation digest after authorization succeeds
and before loading/using a long-term secret. A conflicting reuse fails; an
identical retry resumes the same session or returns its persisted result.

States are `Reserved -> Prepared -> Emitted` or `Rejected/Aborted`. `Prepared`
stores the exact response bytes and transcript under local at-rest protection.
Immediately before `Emitted`, apply the approved authorization freshness rule
again; atomically persist response, token consumption and audit event before
network transmission. A crash before that commit cannot cause a response to
escape; a crash after it returns exactly the same bytes on an allowed retry.
Do not regenerate proof nonces or change the transcript of a persisted attempt.
Revocation/expiry retries must follow the fresh-authorization rule, not automatically
re-emit a previously prepared secret response. Storage rollback protection is
a deployment assumption to qualify, not a benefit obtained from a database API.

Apply prepare-before-send to every DKG and PET round message, not only the
final decryption response. Before any commitment, opening, private share,
accept/fail vote, proof response or transcript-certificate signature escapes,
persist its exact bytes, intended recipient or broadcast role, round/context
digest, and required secret/randomness state atomically. A round key may bind
only one digest; conflicting retries abort rather than sign a second view.
An identical retry reuses the persisted bytes. Persist an abort before starting
a fresh attempt with independent randomness, and retain the old transcript and
exposure record. Inject crashes before and after each durable message boundary;
no network path may bypass this discipline. Durable local locks give honest
non-equivocation, not network agreement or delivery guarantees.

The pinned existing PRE responder consumes JTI after ACP but before later
secret/proof work. Its failures may consume the token. Keep that observed
behavior in the PRE model; the proposed durable state machine is a new handler
contract, not evidence that upstream PRE already persists one-time release.

## Executable checks and ownership

Before code qualification, generate canonical byte vectors using the pinned
native suite and an independent arithmetic oracle. A deterministic, test-only
share vector is `n=5,k=2`, polynomial `p(X)=11+7X`, participant IDs `1..5`,
shares `18,25,32,39,46`, capsule `E=13G`, expected aggregate key `11G` and
opening `143G`. Combining IDs `{1,3}` uses coefficients `{3/2,-1/2}`. Cover all
threshold subsets. These numeric fixtures are not a DKG ceremony or production
randomness. PET fixtures use `M=19G`, `R=13G`, `C=162G`; compare `19G` (equal)
and `20G` (unequal), including a zero individual blind and a deliberately zero
aggregate blind that must abort. Serialized vectors have not yet been produced.

Required negative controls alter one request/roster/epoch/key/ciphertext/
recipient/round binding at a time; duplicate participant IDs; admit `k-1`
shares; substitute a share/proof; skip the commitment round; accept conflicting
round transcripts; accept invalid subgroup/noncanonical encodings; treat an
aborted PET as equality; bypass grant or provenance; emit before durable commit;
and reuse a reserved token for a different operation. Add a cross-request
exposure test that deliberately combines old valid partial points: it must
demonstrate the documented exposure rather than expect metadata to prevent
the group operation. Require intended errors,
restored positive executions and exact source identity, not compiler failures.

Run real participant processes with genuine accepted Transfer/capsule input,
actual authorization and storage adapters, equivocation/withholding, concurrent
identical and conflicting retries, and crashes on both sides of emission
commit. DKG tests include bad private shares, missing accept/fail messages,
bad/missing final openings and recovery, inconsistent roster/transcript and
wrong role/epoch. Absence of a compatible production adapter is a blocked
integration obligation, not permission to replace it with a trusted boolean.

Implementation ownership is small: actual Orbis participant service owns DKG,
authorization and durable emission; existing `orbis-client` owns wire/version
checks; runtime `note_seizure` owns threshold evidence verification and the
consumer join; this repository owns one corresponding Tamarin model and its
runtime trace checks. No new consensus or generic cryptography framework is
proposed. The first approved implementation slice is a disabled, versioned local
evidence verifier and canonical byte vectors. Its deterministic registry fixtures
are not qualified DKG outputs; it cannot authorize, emit or enable live shares.
The handler, DKG service, broadcast adapter and production authorization join
remain blocked on the corresponding design reviews. Published-construction
correspondence and independent cryptographic review remain required before any
production capability is enabled.

## Actual service and next integration boundary

The service owner is [sourcenetwork/orbis-rs at
0a0f935](https://github.com/sourcenetwork/orbis-rs/tree/0a0f935a85cc60e87561a9c7364fa80fdb3332df),
`bin/orbis-node`, not Shieldd's vendored arithmetic. The local inspection checkout
is an unmodified source input; neither acquisition nor the test-only verifier
qualifies an Orbis deployment.

Reuse the existing authenticated Iroh direct streams and public-contribution
codec. Current DKG transport additionally has signed origin contributions,
leader manifests/chunks, conflict evidence and direct repair of omitted public
messages (`dkg/v0/network/public_{publish,batch,repair}.rs`). This is useful
implementation material. However, phase delivery is explicitly unordered and
`session_state::SessionStateManager` retains contributions and private round
state in memory. Its local consistency checks and fault reports are not yet
an established reliable-broadcast implementation or durable STORM round machine.

The proposed minimal integration path, still requiring design approval, is:

1. Keep the existing encrypted Redb backend. Add one bounded encrypted attempt
   record containing round state, randomness, received authenticated inputs and
   exact outbound messages. Serialize updates per attempt and commit the whole
   record before any send. Add an atomic storage update for the token/attempt
   join rather than treating two independent `set` calls as one transaction.
   Existing `LocalStorageKeys` has no such record, and its current API exposes
   separate writes; these are concrete required changes.
2. First qualify the existing signed-contribution/repair transport and add only
   the missing established broadcast adapter there. A candidate is
   [Dolev–Strong authenticated synchronous broadcast](https://epubs.siam.org/doi/10.1137/0212045),
   which uses signature-chain depth tied to `f+1` synchronous rounds. It is not
   an all-participant acknowledgment rule. Its application needs a fixed
   authenticated roster, full ceremony/attempt/round/value binding, durable
   signing state, synchronized starts, checked signature-chain distinctness and
   a stated honest-channel delay bound. In the initial `f=1` profile, both
   communication rounds must finish before delivering a unique value or the
   failure result. The adapter must preserve STORM's exact public-round order,
   accept/fail barrier and final-opening recovery. A timeout constant does not
   prove the synchrony premise, and a local timeout cannot be silently equated
   with a globally agreed abort. This candidate requires separate design and
   fault-trace review before service code.
3. A consensus-backed board is an alternative only after demonstrating why the
   existing transport cannot meet the required contract with the minimal adapter.
   It is not approved production work. The pinned [Vera Orbis module](https://github.com/sourcenetwork/vera/tree/f3a7864e41ba1362e4dad34304fdc3ea3ec15fe9/x/orbis)
   already owns ring membership and finalization, but currently has no public
   protocol-round slots. A bounded `(ring, epoch, ceremony, attempt, round,
   sender)` record and authenticated, first-write-only submission would be new
   functionality in that module. Store the complete bounded public message,
   not merely a hash whose data a malicious sender can withhold. Read only
   verified finalized state; keep private VSS shares on authenticated encrypted
   direct channels. Pin round deadlines to finalized heights and preserve
   STORM's prescribed recovery of missing final openings. Chain ordering does
   not replace computational DKG review or guarantee progress under censorship.
4. Keep release authorization separate from the transcript transport. An immutable
   DKG/PET message is not an irreversible permission to disclose. Each new
   honest release must still evaluate the actual grant and revocation/expiry
   policy. Current Vera `check` provides a backend decision without a verified
   revision. A stronger adapter needs either authenticated state proofs and
   local policy evaluation, or an explicitly trusted locally validating full
   node with a checked chain/height/hash and freshness contract. The present
   RPC wrappers implement neither complete contract. Do not synthesize it from
   a client timestamp, requested height, or unverified `status` response.

Using Bankd finality for that board instead would move public ceremony ownership
away from the existing Vera ring module and require an explicit cross-chain
membership/epoch join. It is not the default merely because Bankd is available.
Neither choice changes grant revocation into an irrevocable permit. If a chain
adapter is rejected, an established Byzantine reliable-broadcast construction
with matching participant/fault bounds must be implemented and qualified over
the existing transports; unanimous transcript signatures alone are insufficient.

## First Tamarin target: existing BLS PRE transport

The first live protocol model will target the actual existing BLS PRE handlers,
separately from the proposed Jubjub disclosure protocol. Keep one maintained
protocol lane; recovered historical theories remain reference contracts, not
parallel certificates. No rule grants a fictional Jubjub PET oracle.

Map model transitions to `pre/v0/service.rs`, `coordinator/handlers.rs`,
`coordinator/verification.rs`, `helpers/jti_replay.rs`, and
`crates/crypto/src/bls12_381/pre.rs`: signed-token validation and exact claims;
independent document/ring resolution; per-node live ACP decision; local JTI
recording; key/share load and encryption-proof verification; re-encryption;
authenticated responder statement; distinct registered share verification;
threshold aggregation; reader decryption. Model trusted-relay actor resolution
explicitly. ACP allow/deny is an environment input tied to the exact operation
and node decision event, not an assumed globally current policy fact.

The actual algebra is `U_i=d*s_i*(Y+R)`, aggregate `U=d*s*(Y+R)`, and reader
recovery `U-x*(d*K)` for `Y=xG`, `R=rG`, `K=sG` (take `d=1` without derivation).
The symbolic threshold-PRE and proof-verification abstraction requires a
separate computational/library argument; protocol lemmas do not prove those
equations secure. Bind the abstraction to actual key epoch, reader key,
ciphertext and derivation, not a fresh session-only name that hides cumulative
exposure. Include reader-key knowledge proof and encryption-context binding in
the explicit cryptographic assumptions and concrete tests.

Initial lemmas cover authenticated request/response correspondence, context and
reader substitution resistance, and local replay rejection while an entry is
resident. Include reachable traces for post-ACP cryptographic failure consuming
a JTI, replay after restart/capacity eviction, and reuse at a previously uninvolved
node. Do not state durable/committee-wide exactly-once release for this source.
Conditional reader confidentiality must name threshold/reader compromise and
prior authorized exposure; local ACP success does not prove global revocation.
Liveness is an independent conditional property requiring available honest
threshold, eventual delivery, usable stored shares and a policy/token interval
long enough to complete; the safety model does not assume successful completion.

Replay will use the existing real PRE coordinator/network fixtures and genuine
BLS encrypt/re-encrypt/recover/decrypt routines, plus real Redb close/reopen where
durability is claimed. Capture branch events and exact request/response digests,
then compare the model trace to actual transitions. Use current network fault
hooks for delay, drop and duplicate behavior. A mock ACP service can validate
handler branching only; final authorization qualification needs the pinned real
Vera adapter and chain. Required semantic controls bypass a context comparison,
one share-proof equation or the local JTI guard and must produce the intended
counterexample/rejection change. Production PRE hardening, when required, is a
separate reviewed patch; never amend the model to hide the existing replay loss.

The first authored lifecycle replay uses the actual service checkout at
`0a0f935a85cc60e87561a9c7364fa80fdb3332df`:

| Model boundary | Actual replay target | Limit |
| --- | --- | --- |
| Concurrent local consumption | `helpers/jti_replay.rs::concurrent_same_jti_has_one_local_winner` | One node's actual lock and guard; no committee-wide guarantee. |
| Live-entry eviction and readmission | `at_capacity_the_oldest_entry_is_evicted` | Actual capped algorithm with cap eight and controlled deadlines; not a million-entry performance test. |
| Another node/new boot has no record | `separate_node_or_boot_guards_do_not_share_replay_state` | Real guard constructors; not an OS-crash recovery test. |
| Failure after ACP consumes JTI | `pre/v0/tests.rs::test_responder_post_authorization_storage_failure_consumes_jti` | Actual responder, JWT, document binding, encryption, reader proof and encrypted storage; ACP/bulletin are test doubles. Exact missing-share-bundle error precedes exact replay rejection. |

These tests and `orbis.spthy` are authored; no compiler, Tamarin, or replay pass
is claimed yet. The failure test deliberately uses a missing share bundle:
malformed document JSON is rejected by the real object-ID parser before ACP and
would not exercise the intended post-guard path.

## Durable origin outbox increment (unqualified implementation)

The actual Orbis `submit_public_contribution` path now has an authored immutable
origin-message journal in its existing encrypted Redb backend. The namespace
includes chain, protocol version, ring, committee digest, ceremony, attempt,
phase and origin. The intent includes the canonical payload but excludes the
generated timestamp/signature. An atomic first-write operation returns the exact
winner bytes to every same-intent retry, and refuses conflicting intent or
corrupt persisted data. Current attempt, committee, leader and hard deadline
are checked again after reservation and before dispatch. The signed timestamp
is report evidence, not a replay expiry policy. This does not restore a DKG
session, its private witnesses, original round schedule or reliable broadcast.
DS relay state must remain separate because it can relay two distinct values.

Tests target actual Redb concurrent writers, reopen, errors immediately before
and after durable commit, byte/count limits, corrupt records, and the actual
local submission path consuming pre-existing signed bytes. A per-call test
pause after actual durable reservation changes the live leader or expires the
attempt, then requires refusal before repair-index visibility or dispatch while
preserving the stored winner. Deterministic commit boundary errors are not a
power-loss experiment. The four local publication tests passed on the exact
historical f1f18 source above. Real remote dispatch and the remaining race/task
paths still need explicit adversarial traces.

The initial limits are 256KiB per signed message, 1024 records and 64MiB stored
ciphertext. Exhaustion refuses new records; existing retries remain available.
There is no eviction or deletion based on ephemeral completion. These are
contributions, not sessions. Temporary maintenance must preserve the complete
journal and use a separately reviewed bounded capacity increase; deleting the
table or recreating a database is not recovery. Long-running production
qualification remains **OPEN**. The newer reviewed candidate adds durable
terminal-attempt rejection and atomic payload retirement. Its three Redb
retirement tests passed on the exact 75bf storage snapshot above; the corresponding
node retirement-manager and expiration-worker tests passed on exact ea353,
and all four publication tests passed on exact f1f18 as recorded above. These
receipts do not transfer to an unexecuted combined source candidate. Repeated
manual limit raises do not complete long-running qualification; no
milestone is promoted by source identity or authoring.

The next retirement boundary must use actual generation identity, not an order
invented for random `AttemptId` bytes. `helpers::derive_refresh_session_id`
binds the durable public polynomial, ring key, roster and threshold;
`message_handlers/session_init.rs::validate_refresh_init` reloads that bundle
and refuses a mismatching ceremony. The reviewed terminal candidate reserves
one of 4096 durable attempt identities at admission. Retirement atomically marks
that exact identity completed or aborted and removes its large public-message
payloads. Exact terminal retries preserve the outcome; conflicting outcomes
fail. Admission, storage reservation and dispatch must all refuse terminal
attempts. **This candidate does not compact terminal membership.** A polynomial
transition A→B→A reuses the original ceremony identity, so comparison against
the current polynomial, or refusal of only A→A, does not establish non-reuse.
Generation compaction requires an explicit anti-reuse contract bound to actual
authenticated preparation and persisted state, plus an A→B→A adversarial test.
Any later bundle promotion/registry transition must be one expected-old-bundle
compare-and-swap transaction. Validation performed before an asynchronous gap
is insufficient. Indefinitely aborted attempts can exhaust bounded membership
and fail closed; bounded storage over repeated benign service generations
remains a qualification requirement. Source-reviewed tests cover actual Redb
precommit/postcommit errors and reopen, concurrent reservation/retirement,
terminal refusal after A→B→A, reserved capacity and legacy-record rejection.
The manager and expiration tests require failed retirement to retain ownership
and cancellation state while denying protocol access. The expiration test also
requires the same worker to retire an independent expired sentinel. Publication
tests require terminal refusal after actual reservation and before dispatch.
The storage tests passed only at the recorded storage identity; manager and
expiration passed on ea353 and publication passed on f1f18. These checks do not
establish safe generation compaction, restored private protocol state or the
missing crypto/authority service boundary.

The existing promotion seam is `refresh_health_check::promote_candidate`, which
currently writes the bundle before removing volatile attempt state. Existing
abort/complete and TTL cleanup alone cannot establish durable retirement.
Fresh-ring and reshare retirement require their own authority and late
reporting/repair review. In particular, reshare's ordinary bulletin read is not
a verified finalized revision and must not inherit the local refresh-generation
argument. Existing encrypted storage excludes rollback by an administrator; an
outbox must not silently claim to add rollback-resistant hardware.

## Synchronous broadcast implementation boundary

The candidate is the original authenticated Dolev–Strong phase protocol, not an
all-signature certificate. Its nested signatures, distinct signer chains,
phase-length acceptance, deterministic processing, at-most-two-value relay and
final unique-value/default rule must be implemented together. Each signed
prefix binds chain, protocol version, ring, fixed roster/configuration,
ceremony, attempt, broadcast instance, origin and value. The actual endpoint
signature verifier and authenticated `CommitteeConfig` route mapping are the
reuse points. `PrepareSession.report_signature` is explicitly used for fault
attribution rather than message acceptance, so it cannot supply a signature
verification premise for this protocol.

The existing Iroh direct peer channels can carry all-peer fanout. Leader gossip
can only be redundant delivery: receiving one leader batch is not agreement.
Before activation, the fixed-profile adapter must reject an invalid fault
budget, missing authenticated membership, or unsupported synchronous schedule.
The delivery bound and bounded start skew remain environment assumptions to
test under explicit configuration, not facts inferred from a successful
Prepare/Begin exchange. Every accepted/relayed state and exact signed outgoing
message must be durably committed before transmission. A node restarting after
a missed deadline is ineligible unless it can recover the journal and schedule
in time; such failures count in the advertised fault budget. A local timeout
never constitutes a committee-wide abort decision.

The DS relay journal is separate from the one-intent origin slot: a correct
relay may sign two different values. Its `f+1` communication phases must fit
inside each selected STORM broadcast round, alongside that construction's
authenticated private channels and explicit `n >= 2t-1` synchrony assumptions.
Acceptance requires real service multiprocess traces for equivocation,
last-phase hidden chains, duplicate signers, delayed messages, bounded honest
delivery, crash before/after journal commit, and late restart; neither the
lifecycle Tamarin model nor a locally checked signature chain supplies these
results. Precise scheduling and durable lifecycle review precede this adapter's
implementation or enablement.

## Unselected service-adapter option (held pending specialist/owner review)

This option is held pending specialist and deployment-owner review; no new
endpoint or production service growth is authorized. It is a design option, not an
enabled endpoint. Keep the existing BLS `Dkg` implementation, `PrepareSession`
and `orbis-dkg-config-v2` behavior intact. At the inspected upstream commit,
`transport.rs::PrepareSession` contains no shared round schedule. Followers
authenticate the canonical leader's Iroh route and recompute the configuration
digest in `network/prepare_participant.rs`; their locally initialized `Instant`
deadlines do not establish a shared STORM round boundary.

If selected after those reviews, one separate, default-disabled encryption
ceremony endpoint would have a versioned `StormPrepare` and the fixed `(5,2,1)`
profile. Its trusted deployment
configuration pins chain/genesis identity, governance ring, key role/epoch,
the exact ordered participant IDs and endpoint public keys, ceremony/attempt
and absolute schedule, and explicit clock/delivery/processing bounds. All five
nodes must be provisioned with the same expected configuration digest;
peer-supplied fields cannot redefine that trust anchor. Admission rejects an
unrecognized digest, wrong local identity, unsupported parameters, late start,
overflow or observed clock regression. A signed timestamp authenticates a
claim about time; it does not prove physical clock accuracy or network bounds.
The initial deployment contract must explicitly supply those assumptions.

Use existing endpoint signing and encrypted QUIC for transport. Each public
protocol round runs the reviewed two-phase DS adapter for every origin; direct
private shares have exact origin/recipient/round/configuration binding and
bounded arrival windows. A local timeout must not be converted into an agreed
abort. The paper's exact missing-message behavior determines the next state.
The deployment scheduler must collect the full eligible inbox and verify
clock eligibility again after durable commit and immediately before sending.

The arithmetic/state machine follows figure 11 of the cited paper: commitment
and private-share generation; share verification and accept/fail; second-NIKE
opening only after acceptance; verified recovery of missing or incorrect
openings; final aggregation. A missing final opening cannot remove its dealer's
contribution. These stages require actual canonical Jubjub operations, not a
symbolic PET or FROST-DKG assumption. Pin `jubjub = 0.10.0` and compatible field
traits to the Shieldd suite; this is new implementation/composition work even
though the group library is reused.

Persist a versioned encrypted attempt record containing the exact predecessor,
secret scalars/private shares, authenticated received evidence and complete
outgoing bytes in one transaction before emission. Reopening resumes only that
record and its original schedule. Retrying cannot resample randomness or
re-sign a different round. The public DS journal alone is insufficient because
it does not persist STORM's private state. Reuse Redb's immediate-durability
transaction discipline, with one explicit bounded transition API rather than
a second persistence framework. Terminal admission protection must remain
consistent with the attempt retirement index.

The current `RingPayload.ring_pk` is consumed as a BLS key. Do not replace it
with a Jubjub encoding or let a coordinator-created registry count as governance
authorization. The child encryption-key registry needs an explicit binding to
the actual ring authority and role/epoch before publication or activation.
Until that consumer and the computational composition review are complete,
the new endpoint remains disabled. Local operator configuration qualifies the
fixed deployment experiment; it does not silently create disclosure rights,
fresh policy state, or production authorization for an accepted Shieldd capsule.

## Pinned Vera authority inventory (source only)

The 2026-09-30 inventory binds selected Vera source at
`f3a7864e41ba1362e4dad34304fdc3ea3ec15fe9` and its declared Raccoon/ACP Core
dependencies; it is not an executed chain proof or deployed-chain identity.
The existing access-ticket implementation queries `/store/acp/key` with raw
key `access_decision/<id>`, composes proof key `/acp/access_decision/<id>`, and
checks IAVL/simple-Merkle operations against the AppHash at query height plus
one. Its block/current-height RPCs explicitly use a trusted node, without a
verified validator/header chain. The source provides a concrete historical
proof codec to qualify, not a finalized authorization guarantee.

Stored decisions bind actor, policy, operations, issued height and expiration
deltas, but contain no policy revision. The live `VerifyAccessRequest` query
computes a separate boolean over ACP state. Decision membership cannot prove
current revocation status, including when a decision precedes a revocation in
the same block. The inspected ticket verifier also does not join the proven
raw decision value to its separately supplied decision object; produced-ID
equality is insufficient because its preimage concatenates fields without
length prefixes. These are source-observed qualification gaps, not executed
exploits or claims about a live endpoint.

Authenticated current authority still needs a verified chain/state anchor,
exact key/value/caller/context correspondence and complete current ACP
evaluation inputs. Ring and node-info records supply committee, threshold,
ring PK, policy, versions and identity mappings; the Ring schema does not
contain the complete public sharing polynomial. Local share-verifier state
must be joined to actual ring/epoch authority separately. The compatible
maintained Jubjub encryption DKG/PET and shared-DKG G2-signing-oracle
computational obligations remain open. This inventory changes no milestone
or endpoint activation status.
