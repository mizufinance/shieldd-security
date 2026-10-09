# Complete Shieldd Transfer assurance after migration

Planning date: 2026-10-02. Runtime target:
`844389ee069e1fb2e576708842d0b389b4d9a44a` (`shieldd.lock`).
Status: reviewed by Claude Code Opus 5.5; required changes incorporated below;
implementation underway with GPT-6.1 Sol. See [review record](transfer-proof-plan-review.md).
This plan expands the previously reduced delivery to complete Transfer. It does
not declare any proof, family, or release gate complete.

User scope clarification: the target is **pre-deployment assurance with explicit
setup assumptions**, not certification of an existing deployment registry. Prove
Shieldd's relation/key selection and API preconditions for correctly generated,
matching keys. A future deployment must supply its concrete setup provenance and
registry identity, but their present absence does not block this conditional proof.
References below to production joins mean the actual production code path and
build configuration; deployment-artifact qualification is a separate later gate.

At this pin, `Registry::load` accepts only a complete `shieldd.pari.keys.v2`
registry whose setup label is `development`. `generate_development` calls setup
sequentially for each compiled family using OS randomness. Prove integration
against that actual accepted format; the label and successful relation checks
do not establish secret erasure or a production ceremony. Correct setup and
required secret handling remain explicit premises. Fresh development keys may
support runtime tests without being promoted to deployment evidence.

## Scope and dependency contract

The user explicitly excludes work belonging in a Pari or Commonware security
repository. Assume the security and functional contracts of the exact pinned,
unmodified upstream implementation: relation compilation, proof knowledge
soundness, committed-input binding, zero knowledge, setup-algorithm and transcript
security. Shieldd's actual key generation, entropy, secret handling, build and
distribution are application obligations, not inherited setup security.
Record the version and contracts consumed; do not re-prove upstream internals,
re-audit their implementation, or wait for upstream formal verification.

Shieldd owns whether its use satisfies those contracts: its relation and witness
construction, local backend patches, application-specific parameters/domains,
field/point/byte encodings, public and committed inputs, registry/key selection,
verifier API and batching configuration, signatures, admission and state effects.
Local modifications do not inherit unmodified-upstream trust. Inventory each
patch: inspection-only changes need noninterference evidence; semantic changes
need a scoped review and tests of the changed guarantees, or removal in Shieldd.
If a modification fundamentally changes a backend guarantee, upstream acceptance
of that exact change or a separately stated unresolved assumption is required;
do not quietly turn this into an upstream proof project or mark it discharged.

The same distinction applies to standard cryptographic primitives. Prove the
equations implemented by Shieldd's gadgets and their current instantiation; name
collision resistance, discrete-log/signature security and standard curve facts
as explicit dependency assumptions. Never use universal hash injectivity or
assume transaction conservation as the conclusion of an opaque signature check.

Full Transfer includes the current construction's disclosure/capsule equations
and the state checks required to accept a Transfer. Broad Bankd settlement,
other circuit families and Orbis release protocols remain separate milestones.
A dependency on those features must be explicit and disabled or qualified before
claiming a deployment that uses them. Historical-nullifier generation and removed
history windows stay retired. Current permanent-nullifier replay rejection,
volume state, snapshot policy, atomicity and durability remain in scope.

## What counts as complete

Produce three separate results and an explicit composition argument:

1. **Circuit soundness:** every arbitrary assignment satisfying the actual pinned
   Transfer relation admits a semantic witness satisfying independently defined
   Transfer semantics, whose statement hash equals the public input and whose
   balance blinding equals the committed input. Include
   the constant column, all input roles, statement and committed balance blinding.
   Do not assume an honest witness or a list of semantic facts already equal to
   the desired conclusion.
2. **Legal-input completeness:** every legal semantic witness has a constructed
   assignment satisfying the full relation, with exact statement/committed inputs.
   Sequential construction preserves shared and non-owned columns. Cover required
   real input, optional real/dummy, regulated/unregulated, self-transfer and all
   actual branch combinations; identify genuinely unreachable combinations.
3. **Accepted transaction consequence:** under the named upstream cryptographic
   contracts and verified Shieldd preconditions, acceptance binds the intended
   action, owner, assets, signatures and proof, and execution yields exactly its
   permitted effects. State-model safety, bounded checking, runtime replay and
   fault tests retain their actual scope; none is called an unbounded Rust
   refinement proof. Privacy claims separately require construction randomness
   and disclosure assumptions, not merely consensus acceptance.

No complete-Transfer label until all component proofs and the production-code
joins use the same runtime commit, features, relation and parameters, and the
key/registry checks enforce the explicitly assumed setup contract. A conditional
pre-deployment result names that contract instead of claiming an actual ceremony
or registry artifact was certified.
Full-system release still depends on the other independently open milestones.

## Starting evidence and hazards

Current Windows checks have passed the ordered raw semantic constructor and its
exact statement/committed-blinding composition, alongside the separate component
constructors and four nullifier/cache models. The repaired finite native field
facts passed 35 modules/584 theorem audits, followed by seven initialization
audits. The coherent PRIMARY DH, encryption and EPK sequence is still running.
Authorization, spend, output and volume inverse constructors are new unchecked
drafts that address coverage of the raw legal-input domain. The volume draft
normalizes inactive private auxiliaries while preserving the exact public
statement and committed blinding; it does not assert full-record equality for
those unconstrained auxiliaries. These results and drafts do not
establish arbitrary-assignment extraction, one full circuit assignment, decoded
Rust correspondence or the accepted-transaction consequence. Current native
suites remain unrun. Use the latest `EXECUTION_PROGRESS.md` header for actual
receipts; the dated queue descriptions below retain their historical scope.

The 2026-10-09 continuation added the exact maintained semantic volume
constructor in `ShielddSecurity.TransferVolumeBranchCompletion`. Its generic
`constructed_volume_semantics` theorem computes volume outputs from independent
legal inputs; canonicality uses the separate `CanonicalCrypto` contract and
explicit blinding/path bounds. The full-record frame preserves all other
witness fields. The Mac worker and coordinator independently checked its 21
theorem audits with matched Lean 4.30.0 and Mathlib; Windows recovered and
reviewed the exact source bytes, installed the module, and queued its own narrow
check behind the active DH job. These are component results. Full-row
construction, arbitrary-assignment soundness, source correspondence and the
accepted-state consequence remain open. See the current `EXECUTION_PROGRESS.md`
header for retained receipts and current execution status.

The same continuation installed the exact
`ShielddSecurity.TransferSemanticStatementCompletion` source. Its witness-to-source
projection agrees unconditionally with all 64 semantic public fields; its codec
composition retains the existing primitive contracts and a global canonical
numeric SDK-constructor contract. Mac kernel checks and native field-order/codec
tests are separately recorded. Windows reviewed the source and received logs and
queued a local check of the unchanged import closure. This does not discharge the
actual decoded Rust object correspondence or the full circuit/state joins.

The continuation also installed the exact routing, output/recovery, encryption
and public-canonicality component sources. Encryption is constructed from raw
seeds and bounded ephemeral/ownership scalars, with explicit computed-point
nonidentity premises. Public canonicality is derived from `CanonicalWitness`
and `CanonicalCrypto`, including the computed balance coordinates; it does not
assume `TransferSem`. Their Mac checks and scoped native tests remain distinct
from the queued Windows checks and the open full-assignment/source/state joins.
The new `TransferStateDelta` child-cache model passed its twelve Windows kernel
audits after a proof-script repair, with definitions and theorem types unchanged.
It remains a functional model with explicit Rust ownership and source joins.
The `TransferNullifierStaging` guard/append model is queued. It preserves duplicate,
sealing, saturating-capacity, pending and durable-read check order, including an
explicit reader-error branch. Their source/refinement obligations are recorded
in [the state correspondence work](transfer-state-correspondence.md).
The additional `TransferNullifierPublicCall` draft covers the public empty-input
return, transaction source ID and enabled durable checks, then composes the
separate body and fee calls to retain all four supplied nullifier identities.
Its ten theorem audits await the existing serial Windows verification lane.
The six additional `TransferNullifierReadVector` draft audits derive complete
ordered results from the per-nullifier read function and propagate read errors.
They retain the separate authentication, fixed-boundary and Rust source joins.
The seven `TransferSemanticTailConstruction` kernel audits assemble the dependent
output, volume, encryption and routing stages over one shared semantic witness.
They derive canonicality and current balance bounds while preserving an explicit
earlier registry/user/authorization/spend interface. The later ordered semantic
constructor derives that interface from raw inputs. This assembly does not
establish full circuit construction or Rust correspondence.
The fifteen `TransferRegistryUserCompletion` kernel audits construct the registry
member/gap asset selection and both final compliance paths from raw legal inputs.
Active lifecycle is computed as `1 + 8 * freezeGeneration`, retaining the full
64-bit generation. User path construction preserves authorization and spend
keys and runs after final sender RNK commitment construction. External tree paths
remain authenticated legal-input premises. Their Windows checks passed after
record-layout and arithmetic proof repairs; they do not qualify raw circuit rows
or Rust witness construction.
The three `TransferInitialWitnessConstruction` draft audits derive an initial
canonical storage record from bounded raw headers, canonical address/RNK
coordinates, both raw RNK commitments and the optional real/dummy selector.
The selector is preserved from the entry point for later spend construction.
Every later computed component has explicit zero storage at this
stage. The draft also proves that this seed fails `TransferSem` because its
asset is zero; membership, authorization, spends and the dependent tail must
still be constructed. This removes an assumed canonical base record from the
construction entry point without promoting semantic or all-row completeness.
The receiver's externally authenticated commitment is retained; regulated
authorization computes the sender's final commitment before path construction.
Its narrow check is queued after the existing native suites.
Windows subsequently checked a fresh initial source after four private
canonicality proof-script corrections; all three audits passed. Definitions,
raw fields, dummy selector and public theorem statements were unchanged.
`TransferSpendBranchCompletion` now derives both spend-slot semantics,
canonicality and a whole-record frame from raw note inputs and authenticated
real-note paths. Its eight Windows audits passed; nullifiers are computed,
including the optional dummy hash. `TransferAuthorizationBranchCompletion`
computes the incoming hash reduction, bounded quotient, randomized action key
and regulated sender commitment. Its eleven Windows audits passed under explicit
canonical-operation and globally scoped group-closure contracts. Zero action
randomizers remain legal when the computed key is nonidentity. These component
constructors have no `SpendSem` or `AuthorizationSem` input premise.
The new `TransferSemanticConstruction` assembles raw initial, registry,
authorization, spend and final compliance inputs before the dependent tail.
Its five Windows kernel audits derive the earlier-component interface, canonicality
and complete semantic witness. It does not construct or
qualify the full pinned circuit assignment, or prove Rust witness correspondence.
The five `TransferUserLifecycleDecomposition` Windows kernel audits recover
the regulated freeze generation and reconstruct the original user record.
The legal inverse chooses zero for the unused unregulated generation, covering
the full inactive lifecycle range. Every canonical `UserSem` record yields a
legal raw path whose construction reproduces that record; existing membership
facts are transported from the semantic premise in this reverse direction.
This establishes semantic input coverage, not full relation completeness or
Rust path authentication.
An immutable serial queue waits for actual successful DH completion before
running the eight prepared Windows component checks, stopping on the first
failure. Waiting does not launch a second heavy verification job.

At the user's request to split builds between Windows and Mac, Windows retains
the active DH controller and Mac owns the separate 31-module, 141-audit fixed
native encryption hash closure. Its two generated dependency views preserve the
exact parameter definition bodies; removed captured rows and SDK-loader proofs
receive no qualification from that check. The original duplicate Windows
controllers remain unlaunched and retired. The successful Mac candidate has now
been received and reviewed, and its proof repairs were applied to the handwritten
source and generator. Regeneration matches all reviewed sources exactly. Fresh
Windows import, square, bridge, PRIMARY replay and later field/encryption recipes
are queued after actual DH and component completion. Their waiting status gives
no Windows kernel credit, and the imported result retains its stated scope.

- The historical source universe is formal commit
  `091143d75e4cf8d03e01e0e11743b0eaa9140283`, runtime
  `5aa0dbd7632257831b345c296458861c52a81b33`.
  `reference/migration.tsv` preserves all 110 requirement IDs and the wider
  findings, assumptions, native acceptance and transaction contracts. Accounting
  is complete; semantic migration is not.
- The old `Transfer/{Semantics,CircuitFacts,Concrete,Refinement,Security}.lean`
  files supply a useful contract structure. Some consequences merely project
  assumed facts; porting those projections is not a circuit or runtime proof.
  Old 45/67-field layouts, Decaf quotient representations, Poseidon377,
  per-slot keys and Groth16/SnarkPack artifacts must not carry forward unchanged.
- Current qualified development evidence is ordered 64-field projection and
  generic permanent-spend gates, with separate F17 semantic omissions and
  structural extractor controls. Runtime-to-row correspondence remains an
  assumption. Older hash, scalar, group, compiler and state results have their
  original diagnostic identities and need applicability checks.
- A clean checkout exists at `C:/src/shieldd-pr160-844389ee`; its HEAD and clean
  status were checked during planning. `.work/shieldd-current` and
  `.work/shieldd-next` are dirty older revisions. Preserve them; do not reset or
  certify them. Integration manifests/default paths require deliberate retargeting.
- The formal working tree has substantial existing uncommitted work. Preserve it,
  distinguish new edits, and never substitute newly generated evidence for an old
  qualified artifact without independent qualification.

## Ordered implementation

### T0 — Make scope, provenance and coverage executable

Use the existing CLI and `assurance.json`, not another runner or claim register.
Enumerate all historical requirements applying to Transfer by expanding
`profile_sets`; route shared/native/protocol obligations from `migration.tsv` and
the historical external-check map as well. Each occurrence keeps its source
selector and receives a current contract, owner, disposition, runtime location,
proof/replay target, controls and open status. Explicitly distinguish replaced,
retired, dependency-assumed, proved, tested and still-open obligations.

Add current-only obligations (Pari committed blinding, keys.v2 registry, single
action-key policy, current encodings and application patches). Cross-check the
actual constructor call graph so historical IDs cannot hide new behavior.
Associate dependency assumptions with their exact upstream version and Shieldd
preconditions; existing backend claims must not silently become proofs.

Extend `security.py check` to reject missing/duplicate mappings, unknown
obligations, retired-history promotion, stale runtime binding and unsupported
completion. Keep family/system/release gates blocked. Add targeted mutation tests
for this policy. Update the existing verification document to point to the plan
and supersede its old reduced-scope priority without rewriting historical results.

Acceptance: reproducible obligation inventory with every applicable old occurrence
and every current constructor assigned; policy tests pass; no proof-status upgrade.

### T1 — Independent current semantics and production boundary

Author small handwritten modules in the one Lean package for current Transfer
semantics, circuit facts, transaction effects and composition. Derive the contract
from reviewed protocol intent and historical requirements, then compare it to
current Rust; do not define the specification as the emitted row conjunction.
Use semantic naturals/integers for amounts and positions, current curve points and
canonical byte conversions. Include exact real/dummy rules, owner/asset sharing,
note and recovery commitments, policy branches, volume/routing, ciphertext fields,
action balance and statement fields. Specify output multiplicity and order.

Separate circuit predicates, native admission predicates, state transitions,
honest-wallet construction facts and imported cryptographic contracts. Keep all
external premises visible in theorem signatures. Define end-to-end result types
without populating them with unproved axioms or treating record assembly as proof.

Capture the actual production feature/configuration and current relation/input
layout. Bind the 64 fields, wrapper, public hash, committed scalar, key registry,
parameter sources and ordinary compiler output. Compare ordinary and observing
constructors including ordered rows, coefficients, constants, roles and exact EOF.
Use upstream compiler correctness as a contract; prove/qualify only Shieldd's
adapter/extraction and any local compiler modifications. Source reading or hashes
alone cannot discharge this semantic correspondence boundary.

Acceptance: audited independent definitions; current row/layout capture; explicit
upstream/application boundary; meaningful field/order/role/row mutation failures.

### T2 — Reusable gadget soundness and constructive completion

Port applicable existing lemmas only after checking premises and dependencies.
Work in dependency order:

| Component | Required result and representative semantic controls |
| --- | --- |
| Range/comparison/volume arithmetic | Canonical bit reconstruction, inclusive comparisons, integer no-wrap, unconditional candidate ranges; overflow, missing bit and comparison endpoint controls |
| Poseidon/hash/tree | Exact current constants, domains, sponge arity/padding, all rounds, leaf preimages and ordered paths; wrong domain/arity/sibling/position controls |
| Scalar reduction | Canonical quotient/remainder, full-width reconstruction/caps and nonzero IVK; quotient wrap, terminal bound and omitted inverse controls |
| Jubjub/group/map | Actual arithmetic, denominators, on-curve/subgroup/nonidentity requirements and canonical coordinate/byte use under explicit standard group contracts; torsion, identity, sign/alias and denominator controls |
| Compiler adapter/local extensions | Shared-wire ownership, deferred-square evaluation and preserving completion for the Shieldd extraction/local changes only; column, role and cross-consumer alias controls |

Use symbolic folds/recurrences and small finite chunks rather than unrolled wide
constraint proofs. Reuse generic upstream contracts where applicable; a generic
lemma or sampled honest witness never substitutes for the actual caller join.

Acceptance per gadget: arbitrary-assignment theorem, constructive completion,
exact selected-current-row join, full premise/axiom audit, positive fixtures and
intended semantic mutation results. Failed builds/timeouts are failures, not controls.

### T3 — Ownership, spends and proof-bound statement

Compose both note paths and nullifier derivations with shared owner/asset, current
permanent-spend gates and optional dummy domain/slot/seed/randomizer binding.
Complete IVK and regulated RNK derivation, sender transmission-key relation,
randomizer constraints and the actual single `rk = ak + [r]G` action key.
Use the upstream knowledge/extraction contract when connecting witness relations
to authorization; mere existence of a randomizer does not establish knowledge.

Ownership and volume-chain uniqueness must account for scalar reduction:
`IVK = H_IVK(nk, ak) mod r`. Equal IVKs for distinct key tuples can arise from
different field hashes separated by a multiple of `r`; this event is not
necessarily a collision in the full-field hash. Derive the needed reduced-key
binding bound under an explicitly named cryptographic model, or retain it as an
unresolved construction assumption. Ordinary field-hash collision resistance
alone does not discharge it. This matters to the undisclosed-volume trace
because its origin nullifier uses `auth.nk` in both regulated and unregulated
branches. Do not assume universal key-derivation injectivity or classify this
unproved security boundary as a demonstrated practical attack.

The exact local arithmetic is `p = 8*r +
43182373549099571680785400801115150921`, with positive remainder below `r`.
Each reduced scalar therefore has at most nine canonical field preimages.
Under an explicitly assumed random-oracle model with uniform field outputs,
one fresh distinct-input query hits a fixed scalar with probability at most
`9/p`; a union bound over `q` distinct queries gives at most
`q*(q-1)*9/(2*p)` for any reduced-output collision. These bounds concern all
queries before filtering zero outputs. Zero has exactly nine field preimages;
conditioning on a nonzero output changes the per-query bound to `9/(p-9)`.
An honest retry construction must account for its queries before that filtering.
These are a possible construction argument,
not a claim that Poseidon has been proved to realize that model. Prove the finite
preimage bound, identify the actual ownership/key game and group preconditions,
and keep the cryptographic model assumption explicit in any resulting theorem.

Join semantic fields to `Statement::fields`, native action extraction, canonical
encodings, the actual public-input hash and committed balance scalar. Audit
required/optional branches and cross-input substitution. Prove completion without
overwriting columns consumed elsewhere. Controls target owner/key/asset swaps,
dummy misuse, nullifier substitution and statement/committed-input mismatches.

Acceptance: one current-source ownership/spend/statement composition, not a bundle
of unrelated slice theorems or old row-count claims.

### T4 — Remaining Transfer semantics and full relation

Prove registry and compliance membership/status/policy branches, paired roots,
thresholds, sender/receiver roles, output/recovery commitments, encryption/audit
equations, routing, volume and self-transfer behavior. Migrate confidentiality
construction requirements with an explicit distinction between accepted equations
and wallet entropy/nonzero randomness. Do not claim Orbis release security here.

Prove signed net amount, exact asset-generator/balance commitment and committed
blinding linkage. A Transfer action need not have net zero value. Compose full
soundness and legal-input completeness over a single shared assignment. Account
for every actual constructor/row as a proved semantic component or constructive
auxiliary; document overlap and prove that shared-variable premises agree.

The pinned test named `all_branches_compile_to_one_relation_and_bind_current_audit_keys`
starts from six fixtures, all with a dummy second input, distinct addresses,
positive change and Ordinary context. Its continuation fixture has zero prior
volume. Supplement those fixtures with a real second input, self-transfer,
FeeFunding, zero change, nonzero continuation and amount/routing boundaries;
record which combinations are reachable. The fixture builder currently computes
ordinary volume outputs regardless of its context field, so a fee-positive case
must use the correct native construction or repair that fixture logic. Passing
the existing test alone does not establish the full branch matrix.

Acceptance: named full-Transfer relation theorems with no hidden desired-fact
premises, full audits and branch/mutation matrix; full relation coverage at this
pin rather than a percentage based on historical theorem counts.

### T5 — Native proof admission, authorization and conservation

Inventory every reachable Transfer acceptance path, including normal, batched,
fallback, cached and fee-funding paths. Bind canonical bytes to exact family,
key, parameter set, action slot, ordered public input and committed input. Qualify
actual claim-binding API use; never inherit a claim for prebound APIs by name.
Review Shieldd patches and application use of batch randomness/fallback; upstream
batch-protocol internals remain assumed.
The current `TransferFullCarrierAcceptance.CompiledClaim` intermediate interface
includes the owned subgroup-order bound on committed blinding. Its instantiation
must derive that bound from the checked canonical-blinding rows and the exact
column-2/shadow-9 link after upstream field-assignment extraction. Treat this
interface as a combined result; do not import the bound as a Pari assumption.
The checked scalar-range and committed-link component theorems provide the
local ingredients, while full-relation projection and canonical representative
identity still require their exact composition.
Full raw-byte equality makes cache reuse independent of collisions in the
transaction lookup hash. Registry-ID equality has a separate boundary: the ID
hashes the suite, families and verifying-key digests, so matching IDs require
the named collision-security contract to identify the same key registry.

Join canonical/nonidentity keys, the actual RedDSA verifier variant and complete
effect/auth hash construction. The witness anchor is excluded from effect data;
prove its independent context equality and state admissibility. Cover all action,
fee, parameter, order and payload bindings. Derive transaction per-asset
conservation from circuit balances and the named binding-signature/group contract,
including all action/fee terms and multiplicities, not a no-inflation axiom.
The circuit permits canonical zero blinding. A proof-bearing transaction must
still have a nonidentity aggregate binding verification key under the native
admission rule. Keep circuit completeness separate from transaction
constructibility; do not invent a nonzero action-blinding constraint or assume
that every circuit-legal witness already satisfies transaction admission.

Acceptance: real proof/signature positive tests; semantic wrong-key/family/slot,
malformed encoding, reordered action, altered commitment and cached-context
controls; independently reviewed conditional composition to native acceptance.

### T6 — Permanent state, execution and recovery

Extend the existing Quint model with exact permanent spend/volume uniqueness,
intra-action/intra-transaction duplicates, anchor and paired snapshot/freeze
checks, cache invalidation and execution-time rechecks. Model exact note/output,
nullifier, volume, routing and transaction-index effects and failure rollback.
Preserve the documented fee-funding timing: validate its compliance preconditions
against pre-transaction roots before body actions, then apply its effects after
the body. Ordinary Transfers validate immediately before their effects. An exact
action-bound capability is not a proof that arbitrary later state still satisfies
its earlier preconditions; establish the allowed intervening actions and the
checks performed when effects are applied for each path.
The current documented compliance policy admits the current user/asset root pair
or a recorded pair within the inclusive configured grace window and current freeze
epoch. It forbids mixing snapshots, disables historical admission when the window
is zero, and prevents unfreeze from reviving pre-freeze snapshots. Replace the
historical current-root-only contracts explicitly; qualify these rules against
the native admission and execution paths.
The unfreeze argument needs both branches of admission: unfreeze retains the
incremented per-user freeze generation in the authenticated lifecycle, so the
old leaf differs and root reuse would require the named hash-collision event;
the advanced global epoch separately rejects the old historical snapshot.
An epoch lemma assuming that the requested pair is noncurrent does not alone
establish this complete consequence.
Prove any claimed unbounded abstract invariants separately; label TLC bounds.

Replay traces through real Rust admission and delivery with genuinely verified
artifacts. Exercise commit/rollback/restart and reopen the same persistent database.
Define the fault model and deterministic injection boundaries; include all stores
participating in Transfer commit, cross-action partial failure, duplicate delivery
and crashes around publication. State explicitly where process-kill or power-loss
behavior has not been tested. Broad consumer settlement is a separate obligation.

Acceptance: bound-labelled model results, actual storage projections after each
step, intended semantic bypass/rollback controls and a precise remaining
implementation-correspondence assumption. No runtime test becomes a Rust theorem.

### T7 — Independent closure and atomic evidence refresh

Review complete theorem conclusions, premises and axioms, requirement/constructor
coverage, local patch dispositions, dependency contracts, negative-control causes
and production input/key/caller/state joins. No `sorry`, `admit`, unsound axioms,
unbounded heartbeats, vacuous legal-input domain or global hash injectivity.

Only then use the existing atomic refresh protocol to publish new exact-source
evidence and separately link independently qualified receipts. Handwritten proof,
generator and policy edits precede generated artifacts and should be separate
commits when practical. A lock/build/parameter/key change invalidates affected
joins. Update a Transfer-specific gate only after its complete evidence is
validated; keep all other family/system gates open until their own milestones.
Do not remove the pilot's fail-closed gate merely to allow a green result.

Acceptance: independently reviewed conditional full-Transfer assurance at the
exact clean pin, with reproducible commands, retained raw evidence, explicit
assumptions and limitations. Publication/push/PR work is outside this request.

## Required refinements from Opus review

These requirements refine the stage descriptions above and are part of their
acceptance gates. The review is a source/plan review, not verification of external
cryptographic claims or execution of any proposed proof.

1. **T0/T1/T5: setup provenance.** Inspect the actual upstream setup contract and
   Shieldd's key-generation procedure. Record production versus development keys,
   exact generation command/build/patches, entropy and any toxic-waste handling
   requirement of that construction. Record unverifiable secret destruction as
   an explicit deployment assumption, not a discharged test. The user accepts
   correctly generated setup as a premise for this pre-deployment target. Join
   keys used in runtime tests to the exact relation and registry, and state the
   general key-matching precondition. Upstream setup-algorithm security remains
   assumed; proving it is not a task here.
2. **T1/T3: primary soundness anchor.** Compute the relation digest of the actual
   exported rows using the contracted upstream algorithm and match the production
   Transfer key selected from keys.v2. Verify public/committed/constant roles.
   Prove `forall assignment, RowsHold assignment -> exists semanticWitness,
   TransferSem semanticWitness /\ statementHash semanticWitness = publicInput
   assignment /\ blinding semanticWitness = committedInput assignment`.
   This is a specification shape, not an authored unproved Lean theorem. It still
   requires faithful coefficient/field/layout serialization and the digest-binding
   assumption; hashes do not establish semantics. Soundness should reconstruct
   meanings from actual rows rather than assume source labels are correct.
   Constructor/source correspondence separately supports completeness and the
   Rust prover. For this pre-deployment target, quantify over matching keys and
   registries under the explicit setup contract and verify that actual loading
   and selection enforce relation equality. Fresh development artifacts can
   exercise that path; they do not certify a deployed registry. The concrete
   deployment-artifact join remains a separate later gate.
3. **T0/T5: composable imported contract.** Name adaptive multi-instance and
   multi-statement extraction, actual Fiat-Shamir use, and fresh-coefficient batch
   verification. Require simulation-extractability only if the stated security
   game uses simulated proofs. Identify unsupported guarantees as unresolved
   dependency assumptions, never as a new upstream implementation/proof project.
4. **T1/T5/T6: registry invariants.** Account for ordered/unique indexed leaves,
   authorized asset/user admission, nonidentity/valid policy/audit keys, native
   timestamp/day-start freshness and cross-index consistency. Each has an explicit
   admission owner, evidence and composition premise. Transfer cannot assume these
   facts merely because a Merkle path exists.
5. **T2/T4/T5: both scalar moduli.** Specify the signed-magnitude/effective-scalar
   map from BLS12-381 field values to Jubjub scalars; prove circuit/native agreement
   for negative net amounts and blinding. Join the binding-signature secret to
   that map. State an explicit maximum transaction size/amount/fee bound preventing
   wrap in the group order, and test field-negation and noncanonical blinding
   mutants. If runtime permits no such bound, derive the necessary bound or report
   the missing application invariant.
6. **T5: conservation scope.** First claim transactions containing Transfer and
   Transfer-shaped fee funding only. Mixed-family conservation is conditional on
   an explicit correct-balance contract for every other action family. Track
   `ushieldd` fee-asset and retained-fee escrow accounting; broad Bankd settlement
   remains outside this delivery. No unconditional mixed-family conservation.
7. **T0/T3/T5: committed-input consumers.** Enumerate native readers of the
   Transfer commitment. If none consume it, retain its exact balance-variable
   layout binding without inventing an additional application security role.
   If consumers exist, qualify each join. Opening freshness and hiding belong to
   the honest-construction privacy contract, not an inference from length one.
8. **T1/T4/T6: volume history.** Define whether the daily limit is per address or
   owner, unique initialization, parallel chains and multiple actions/transactions
   per block, allowed proof-context values on self/external branches, and the use
   of `nk` versus `effective_nk`. The pinned intent source
   `docs/compliance/flow.md#daily-volume-state` limits **undisclosed** outbound
   volume: explicit disclosure/over-limit padding flags only the current Transfer
   and leaves the real accumulator unchanged. Do not prove a false cap on total
   daily outbound value. Establish the trace-level undisclosed-volume invariant
   with explicitly labelled proof/model/replay evidence. Volume nullifiers have
   separate day-scoped pruning; retiring spend-history windows does not retire it.
9. **T1/T4: intent discrepancies.** Historical semantic/requirement sources above
   and pinned Shieldd `docs/circuits.md`, `docs/compliance/flow.md`,
   `docs/proof-system.md`, `docs/nullifier-history.md`, `docs/routing.md`, `docs/wallet.md` and
   `docs/jubjub-external-contract.md` are evidence of intent, not automatic
   authority for new choices. Record how routing from change amount, encryption
   of receiver amount, unregulated audit-key defaults, changed role-swapping
   policy and other semantic differences follow the named current contracts.
   `docs/routing.md` specifies receiver plus change-owner/filler for unregulated
   transfers, and sender plus receiver for regulated transfers. Obtain an owner
   decision only for a genuinely contradictory or underspecified contract.
   Unresolved intent keeps dependent spec acceptance open; do not silently copy
   the Rust.
10. **T3/T6: dummy effects.** State whether dummy and volume-padding nullifiers
    enter permanent or day-scoped state and how this affects uniqueness/replay
    and growth. Pinned `docs/nullifier-history.md` includes padding and fee spend
    nullifiers in the permanent log, while `docs/compliance/flow.md` distinguishes
    day-scoped volume nullifiers; verify the actual corresponding paths.
    Establish disjoint domain/preimage encodings; collision resistance supplies
    only a computational collision bound, never absolute hash-range disjointness.
11. **T2: scalable certificates.** Prove parameterized gadget templates once and
    transport them by checked column renaming. Use a sound Lean checker/reflective
    matching certificate or equivalent symbolic substitution lemmas for actual
    instances. Validate all row coefficients/roles/sharing; unknown matches fail.
    No `native_decide` or trusted-compiler axiom. Start with a representative hash
    and group instance under a finite stage budget before expanding. On pressure
    stop; repair chunking/sharing rather than rerun with unbounded resources.
12. **T1/T4: honest-construction privacy.** Define allowed public leakage (including
    policy/timestamp/routing/volume/shared action-key data), fresh action nonce
    roots, nonzero tier scalars, commitment openings and fixed unregulated-key
    secrecy assumptions. Current `encryption.rs` constrains each canonical tier
    scalar's EPK to be nonidentity, and `audit.rs` constrains the ownership
    randomness commitment to be nonidentity. Derive the corresponding nonzero
    consequences under the group contract; do not inherit the historical
    wallet-only nonzero boundary. Freshness and unpredictability remain honest
    construction premises. Keep equations, wallet entropy facts and computational
    confidentiality separate. Confidentiality is conditional on these contracts;
    consensus soundness alone does not establish it.
13. **T5: transcript/application binding.** Record the upstream contract for key
    and claim absorption plus Shieldd's suite/family context; qualify cross-key
    and cross-family rejection. Determine which proof bytes affect effect/auth
    hashes and transaction IDs, and the consequences for malleability, caching
    and duplicate transaction indexing.
14. **All stages: explicit dependencies.** Every deliverable records its unmet
    `conditional_on` obligations. Completion of a composition is refused while
    any required join is open. An approved dependency assumption remains labelled
    assumed and appears in the final conditional claim; unresolved assumptions
    cannot be disguised as approved or verified.
15. **T1/T4: runtime completeness testing.** In addition to a mathematical
    constructive completion, test that the actual Rust witness/prover path
    satisfies the captured relation for each reachable branch, with exact
    input/statement/commitment agreement. This is runtime testing, not a universal
    correctness proof of Rust witness generation.

## Execution and review protocol

Claude Code `claude-opus-5-5` reviews this plan and its boundary before implementation.
Retain its actual response/model metadata and repair material objections. Then
delegate implementation to `gpt-6.1-sol` with the reviewed plan and findings.
Start at T0/T1, continue through dependencies, and report actual accomplishments
and remaining obligations rather than declaring this multi-stage project complete
after scaffolding. Any unavailable runtime hooks/toolchains or memory limits must
be reported precisely; continue independent source work where useful.

One heavy verification job at a time per physical host across all agents;
the explicitly requested Windows/Mac split uses disjoint owned jobs. Use the established
toolchain with its exact version recorded; native Windows Lean is also available
and avoids the observed WSL host-memory pressure for these narrow modules.
Run one `lake` process with
`LEAN_NUM_THREADS=1`, narrow named modules, finite stage budgets and memory
monitoring that stops this task's jobs on pressure. Full replay belongs to final
closure. Read-only review and lightweight policy tests may precede it. Never reset
existing dirty work, install a parallel proof stack, or commit caches/logs/workspaces.
