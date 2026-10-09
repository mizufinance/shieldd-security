import ShielddSecurity.TransferFullCarrierAcceptance
import ShielddSecurity.TransferReduction

set_option maxHeartbeats 300000

namespace ShielddSecurity.TransferFieldClaimAcceptance

open TransferAcceptance TransferAdmission TransferProjection TransferSourceBridge TransferTransaction

/-! Minimal primitive knowledge extracts field coordinates and exact satisfying rows.
Natural public canonicality and the subgroup bound are locally derived afterwards.
OwnedRange is an explicit pending local row theorem, never an upstream guarantee.
The global field codec/opening interpretation still needs pinned SDK correspondence.
Full row soundness, native acceptance and durable state refinement remain OPEN. -/

def FieldClaim {F : Type} [Field F] (rows : List Row) (publicLc committed : Linear)
    (opensField : List Nat → F → Prop) (item : Item) (claim : ClaimContext) : Prop :=
  ∃ rho : Nat → F, rho 0 = 1 ∧ Satisfies rho rows ∧
    eval rho publicLc = (item.statement : F) ∧
    opensField claim.commitments (eval rho committed)

structure UpstreamFieldKnowledge {F : Type} [Field F] (input : TransferFullCarrierAcceptance.Inputs)
    (rows : List Row) (publicLc committed : Linear)
    (opensField : List Nat → F → Prop) : Prop where
  individual : ∀ item claim relation,
    input.decodeEnvelope item.envelope = some claim →
    input.registry.relation item.family = some relation →
    ClaimBound item.family relation item.statement claim → input.individual item = true →
    FieldClaim rows publicLc committed opensField item claim
  batch : ∀ (first : TransferProofAdmissionModel.Entry) rest relation,
    input.registry.relation first.item.family = some relation →
    (∀ entry ∈ first :: rest, input.decodeEnvelope entry.item.envelope = some entry.claim) →
    (∀ entry ∈ first :: rest, TransferProofAdmissionModel.ContextBound first.item.family relation entry) →
    input.batch ((first :: rest).map TransferProofAdmissionModel.Entry.item) = true →
    ∀ entry ∈ first :: rest, FieldClaim rows publicLc committed opensField entry.item entry.claim

/-- Global interpretation of a natural opening value through the field encoding. -/
def naturalOpening {F : Type} [Field F] (opensField : List Nat → F → Prop)
    (commitments : List Nat) (value : Nat) : Prop := opensField commitments (value : F)

/-- Owned proof obligation on rows, separate from upstream knowledge. M15 discharges
the analogous predicate for its coherent local block. Complete row inclusion and
representation correspondence are still required before applying it here. -/
def OwnedRange {F : Type} [Field F] (codec : TransferReduction.CanonicalField F)
    (rows : List Row) (committed : Linear) : Prop :=
  ∀ rho : Nat → F, rho 0 = 1 → Satisfies rho rows →
    codec.decode (eval rho committed) < TransferCore.scalarOrder

theorem promote_field_claim {F : Type} [Field F]
    (codec : TransferReduction.CanonicalField F) (rows : List Row) (publicLc committed : Linear)
    (opensField : List Nat → F → Prop) (range : OwnedRange codec rows committed)
    (item : Item) (claim : ClaimContext) (publicCanonical : item.statement < TransferCore.fieldModulus)
    (fieldClaim : FieldClaim rows publicLc committed opensField item claim) :
    TransferFullCarrierAcceptance.CompiledClaim (F := F) rows publicLc committed (naturalOpening opensField) item claim := by
  obtain ⟨rho, one, satisfied, publicEq, opening⟩ := fieldClaim
  refine ⟨rho, codec.decode (eval rho committed), one, satisfied, publicEq,
    (codec.roundtrip _).symm, publicCanonical, range rho one satisfied, ?_⟩
  simpa only [naturalOpening, codec.roundtrip] using opening

theorem expected_statement_canonical {T B : Type} (model : TransferFullCarrierAcceptance.Model T B)
    (crypto : TransferSem.Crypto) (canonical : TransferSem.CanonicalCrypto crypto)
    (family : Nat) (carrier : TransferNativeSignaturePolicy.Carrier T) (index : Nat) :
    (TransferFullCarrierAcceptance.expected model crypto family carrier index).statement < TransferCore.fieldModulus := by
  exact canonical.1 .transferStatement (model.fields (model.extract carrier.body index).body)

theorem verified_field_claims {F : Type} [Field F] (input : TransferFullCarrierAcceptance.Inputs)
    (rows : List Row) (publicLc committed : Linear) (opensField : List Nat → F → Prop)
    (knowledge : UpstreamFieldKnowledge input rows publicLc committed opensField)
    (entries : List Item) (capabilities : List Capability)
    (success : TransferFullCarrierAcceptance.verifyForMode input.verificationMode input.decodeEnvelope input.registry
      input.individual input.batch entries = some capabilities) :
    ∀ item ∈ entries, ∃ claim, input.decodeEnvelope item.envelope = some claim ∧
      FieldClaim rows publicLc committed opensField item claim := by
  apply TransferFullCarrierAcceptance.mode_checks_success input.verificationMode input.decodeEnvelope input.registry input.individual
    input.batch (fun item => ∃ claim, input.decodeEnvelope item.envelope = some claim ∧
      FieldClaim rows publicLc committed opensField item claim) ?_ ?_ entries capabilities success
  · intro item capability checked
    obtain ⟨claim, relation, decoded, lookup, bound, verified, _⟩ :=
      TransferEnvelopeSourceBridge.individual_envelope_join _ _ _ _ _ checked
    exact ⟨claim, decoded, knowledge.individual item claim relation decoded lookup bound verified⟩
  · intro first rest caps checked item inside
    obtain ⟨entry, tail, relation, _, source, decoded, lookup, contexts, verified, _, _⟩ :=
      TransferEnvelopeSourceBridge.batch_envelope_join _ _ _ _ _ checked
    have member : item ∈ (entry :: tail).map TransferProofAdmissionModel.Entry.item := source.symm ▸ inside
    obtain ⟨native, present, same⟩ := List.mem_map.mp member
    subst item
    exact ⟨native.claim, decoded native present,
      knowledge.batch entry tail relation lookup decoded contexts (source.symm ▸ verified) native present⟩

theorem preparation_compiled_claims_from_field_knowledge {T B F : Type} [Field F]
    (model : TransferFullCarrierAcceptance.Model T B) (crypto : TransferSem.Crypto)
    (canonical : TransferSem.CanonicalCrypto crypto) (input : TransferFullCarrierAcceptance.Inputs) (environment : TransferFullCarrierAcceptance.Environment)
    (codec : TransferReduction.CanonicalField F) (rows : List Row) (publicLc committed : Linear)
    (opensField : List Nat → F → Prop)
    (knowledge : UpstreamFieldKnowledge input rows publicLc committed opensField)
    (range : OwnedRange codec rows committed) (raw : List Nat) (prepared : TransferFullCarrierAcceptance.Prepared T)
    (success : TransferFullCarrierAcceptance.prepare model crypto input environment raw = some prepared) :
    ∀ index ∈ model.slots prepared.carrier.body, ∃ claim,
      input.decodeEnvelope (TransferFullCarrierAcceptance.expected model crypto input.family prepared.carrier index).envelope = some claim ∧
      TransferFullCarrierAcceptance.CompiledClaim (F := F) rows publicLc committed (naturalOpening opensField)
        (TransferFullCarrierAcceptance.expected model crypto input.family prepared.carrier index) claim := by
  have facts := TransferFullCarrierAcceptance.preparation_success model crypto input environment raw prepared success
  have claims := verified_field_claims input rows publicLc committed opensField knowledge _ _ facts.2.2.1
  intro index inside
  obtain ⟨claim, decoded, realized⟩ := claims (TransferFullCarrierAcceptance.expected model crypto input.family prepared.carrier index)
    (List.mem_map.mpr ⟨index, inside, rfl⟩)
  exact ⟨claim, decoded, promote_field_claim codec rows publicLc committed opensField range _ claim
    (expected_statement_canonical model crypto canonical input.family prepared.carrier index) realized⟩

theorem preparation_semantic_or_collision_from_field_knowledge {T B F : Type}
    [Field F] [CharP F TransferCore.fieldModulus]
    (model : TransferFullCarrierAcceptance.Model T B) (crypto : TransferSem.Crypto)
    (canonical : TransferSem.CanonicalCrypto crypto) (input : TransferFullCarrierAcceptance.Inputs) (environment : TransferFullCarrierAcceptance.Environment)
    (codec : TransferReduction.CanonicalField F) (rows : List Row) (publicLc committed : Linear)
    (opensField : List Nat → F → Prop)
    (knowledge : UpstreamFieldKnowledge input rows publicLc committed opensField)
    (range : OwnedRange codec rows committed)
    (soundness : TransferFullCarrierAcceptance.LocalRowSoundness (F := F) crypto rows publicLc committed (naturalOpening opensField))
    (raw : List Nat) (prepared : TransferFullCarrierAcceptance.Prepared T)
    (success : TransferFullCarrierAcceptance.prepare model crypto input environment raw = some prepared) :
    ∀ index ∈ model.slots prepared.carrier.body,
      TransferFullCarrierAcceptance.SemanticOrCollision model crypto (model.extract prepared.carrier.body index) := by
  have claims := preparation_compiled_claims_from_field_knowledge model crypto canonical input environment
    codec rows publicLc committed opensField knowledge range raw prepared success
  intro index inside
  obtain ⟨claim, _, rho, blinding, one, satisfied, publicEq, committedEq, publicBound, scalarBound, opening⟩ :=
    claims index inside
  obtain ⟨witness, semantic, _, statement⟩ :=
    soundness _ claim rho blinding one satisfied publicEq committedEq publicBound scalarBound opening
  refine ⟨witness, semantic, ?_⟩
  by_cases same : model.fields (model.extract prepared.carrier.body index).body =
      TransferSem.publicFields crypto witness
  · exact Or.inl same
  · exact Or.inr ⟨same, statement⟩

theorem full_carrier_consequence_from_field_knowledge {T B F : Type}
    [Field F] [CharP F TransferCore.fieldModulus]
    (model : TransferFullCarrierAcceptance.Model T B) (crypto : TransferSem.Crypto)
    (canonical : TransferSem.CanonicalCrypto crypto) (input : TransferFullCarrierAcceptance.Inputs) (environment : TransferFullCarrierAcceptance.Environment)
    (codec : TransferReduction.CanonicalField F) (rows : List Row) (publicLc committed : Linear)
    (opensField : List Nat → F → Prop)
    (knowledge : UpstreamFieldKnowledge input rows publicLc committed opensField)
    (range : OwnedRange codec rows committed)
    (soundness : TransferFullCarrierAcceptance.LocalRowSoundness (F := F) crypto rows publicLc committed (naturalOpening opensField))
    (mode : TransferIndexing.Mode) (state after : TransferIndexing.State)
    (transaction : Nat) (raw : List Nat) (prepared : TransferFullCarrierAcceptance.Prepared T)
    (success : TransferFullCarrierAcceptance.run model crypto input environment mode state transaction raw = some (prepared, after)) :
    TransferFullCarrierAcceptance.Consequence model crypto input environment mode state after transaction raw prepared := by
  obtain ⟨checked, facts, effectResult⟩ := TransferFullCarrierAcceptance.full_carrier_pending_effects model crypto input environment
    mode state after transaction raw prepared success
  have canonicalBound := TransferFullCarrierAcceptance.preparation_canonical_and_bound model crypto input environment raw prepared checked
  have signatureArguments := TransferFullCarrierAcceptance.preparation_signature_arguments model crypto input environment raw prepared checked
  exact ⟨canonicalBound.1, facts.2.1.1, facts.2.1.2.1, canonicalBound.2,
    signatureArguments.1, signatureArguments.2, facts.2.1.2.2.2.1,
    TransferFullCarrierAcceptance.preparation_current_slots model crypto input environment raw prepared checked,
    preparation_semantic_or_collision_from_field_knowledge model crypto canonical input environment
      codec rows publicLc committed opensField knowledge range soundness raw prepared checked, effectResult⟩

set_option pp.all true in
#check @FieldClaim
#print axioms FieldClaim
set_option pp.all true in
#check @UpstreamFieldKnowledge.mk
#print axioms UpstreamFieldKnowledge.mk
set_option pp.all true in
#check @OwnedRange
#print axioms OwnedRange
set_option pp.all true in
#check @promote_field_claim
#print axioms promote_field_claim
set_option pp.all true in
#check @expected_statement_canonical
#print axioms expected_statement_canonical
set_option pp.all true in
#check @verified_field_claims
#print axioms verified_field_claims
set_option pp.all true in
#check @preparation_compiled_claims_from_field_knowledge
#print axioms preparation_compiled_claims_from_field_knowledge
set_option pp.all true in
#check @preparation_semantic_or_collision_from_field_knowledge
#print axioms preparation_semantic_or_collision_from_field_knowledge
set_option pp.all true in
#check @full_carrier_consequence_from_field_knowledge
#print axioms full_carrier_consequence_from_field_knowledge

end ShielddSecurity.TransferFieldClaimAcceptance
