import ShielddSecurity.TransferNativeMixedJoin

set_option maxHeartbeats 250000

namespace ShielddSecurity.TransferNativeSourceCatalogue

open TransferNativeCarrierBridge TransferNativeSignaturePolicy TransferSourceBridge TransferProjection

/-! One retained typed source supplies mixed-body occurrence order and every
Transfer signature argument. Complete canonical action and transaction bytes
remain stored alongside the public/effect views; they are never recovered from
an Item digest. The Rust decoder must establish that those views and bytes
describe the same native values. Native key/group decoding and cryptographic
signature security remain separate; no successful verifier Bool is interpreted
as spend ownership. This is a source constructor model, not a Rust refinement. -/

structure TransferSource where
  source : SourceSlot ActionView
  key : Nat
  signature : List Nat
  canonicalActionBytes : List Nat

def spend (transfer : TransferSource) : Spend :=
  ⟨transfer.key, transfer.source.body.bodyAnchor, transfer.signature⟩

inductive SiblingKind where
  | reshape | withdrawal | registerAsset | registerUser

def SiblingKind.kind : SiblingKind → TransferMixedBody.Kind
  | .reshape => .reshape
  | .withdrawal => .withdrawal
  | .registerAsset => .registerAsset
  | .registerUser => .registerUser

structure SiblingSource where
  kind : SiblingKind
  source : SourceSlot ActionView
  signatures : List Spend
  canonicalActionBytes : List Nat

inductive Action where
  | transfer (value : TransferSource)
  | sibling (value : SiblingSource)

structure Body where
  actions : List Action
  funding : Option TransferSource
  canonicalBodyBytes : List Nat

def Action.spends : Action → List Spend
  | .transfer value => [spend value]
  | .sibling value => value.signatures

def bodyOccurrences (start : Nat) : List Action → List (Nat × TransferSource)
  | [] => []
  | .transfer transfer :: rest => (start, transfer) :: bodyOccurrences (start + 1) rest
  | .sibling _ :: rest => bodyOccurrences (start + 1) rest

def occurrences (body : Body) : List (Nat × TransferSource) :=
  bodyOccurrences 0 body.actions ++ body.funding.toList.map (fun transfer => (body.actions.length, transfer))

def signatureArguments (body : Body) : List Spend :=
  body.actions.flatMap Action.spends ++ body.funding.toList.map spend

def locate (slot : Slot) (transfer : TransferSource) : SourceSlot ActionView :=
  { transfer.source with location := slot }

def mixedFrom (start : Nat) : List Action → List (TransferMixedBody.Action (SourceSlot ActionView))
  | [] => []
  | .transfer transfer :: rest =>
      ⟨.transfer, locate (.bodyAction start) transfer⟩ :: mixedFrom (start + 1) rest
  | .sibling sibling :: rest =>
      ⟨sibling.kind.kind, { sibling.source with location := .bodyAction start }⟩ ::
        mixedFrom (start + 1) rest

def mixedBody (body : Body) : List (TransferMixedBody.Action (SourceSlot ActionView)) :=
  mixedFrom 0 body.actions

def mixedFee (body : Body) : Option (SourceSlot ActionView) :=
  body.funding.map (locate .feeFunding)

def bodySourceFrom (start : Nat) (fallback : Nat → SourceSlot ActionView) :
    List Action → Nat → SourceSlot ActionView
  | [], index => fallback index
  | action :: rest, index =>
      if index = start then
        match action with
        | .transfer transfer => locate (.bodyAction start) transfer
        | .sibling _ => fallback index
      else bodySourceFrom (start + 1) fallback rest index

def extracted (fallback : Nat → SourceSlot ActionView) (body : Body) (index : Nat) : SourceSlot ActionView :=
  if index = body.actions.length then
    match body.funding with
    | some transfer => locate .feeFunding transfer
    | none => fallback index
  else bodySourceFrom 0 fallback body.actions index

theorem locate_preserves_full_source (slot : Slot) (transfer : TransferSource) :
    (locate slot transfer).body = transfer.source.body ∧
    (locate slot transfer).envelope = transfer.source.envelope ∧
    (locate slot transfer).route = transfer.source.route ∧
    (locate slot transfer).location = slot := ⟨rfl, rfl, rfl, rfl⟩

theorem mixed_body_length (start : Nat) (actions : List Action) :
    (mixedFrom start actions).length = actions.length := by
  induction actions generalizing start with
  | nil => rfl
  | cons action rest ih =>
      cases action <;> simp only [mixedFrom, List.length_cons, ih]

theorem body_original_indices (start : Nat) (actions : List Action)
    (entry : Nat × TransferSource) (inside : entry ∈ bodyOccurrences start actions) :
    start ≤ entry.1 ∧ entry.1 < start + actions.length := by
  induction actions generalizing start with
  | nil => simp only [bodyOccurrences, List.not_mem_nil] at inside
  | cons action rest ih =>
      cases action with
      | transfer transfer =>
          rcases List.mem_cons.mp inside with same | later
          · subst entry
            simp only [Prod.fst, List.length_cons]
            omega
          · have bounds := ih (start + 1) later
            simp only [List.length_cons]
            omega
      | sibling sibling =>
          have bounds := ih (start + 1) inside
          simp only [List.length_cons]
          omega

theorem body_occurrence_source (start : Nat) (actions : List Action)
    (entry : Nat × TransferSource) (inside : entry ∈ bodyOccurrences start actions) :
    Action.transfer entry.2 ∈ actions := by
  induction actions generalizing start with
  | nil => simp only [bodyOccurrences, List.not_mem_nil] at inside
  | cons action rest ih =>
      cases action with
      | transfer transfer =>
          rcases List.mem_cons.mp inside with same | later
          · subst entry
            exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih (start + 1) later)
      | sibling sibling => exact List.mem_cons_of_mem _ (ih (start + 1) inside)

theorem body_source_extraction (start : Nat) (fallback : Nat → SourceSlot ActionView)
    (actions : List Action) (entry : Nat × TransferSource)
    (inside : entry ∈ bodyOccurrences start actions) :
    bodySourceFrom start fallback actions entry.1 = locate (.bodyAction entry.1) entry.2 := by
  induction actions generalizing start with
  | nil => simp only [bodyOccurrences, List.not_mem_nil] at inside
  | cons action rest ih =>
      cases action with
      | transfer transfer =>
          rcases List.mem_cons.mp inside with same | later
          · subst entry
            simp only [bodySourceFrom, if_pos rfl, if_true]
          · have bounds := body_original_indices (start + 1) rest entry later
            have different : entry.1 ≠ start := by omega
            simpa only [bodySourceFrom, if_neg different] using ih (start + 1) later
      | sibling sibling =>
          have bounds := body_original_indices (start + 1) rest entry inside
          have different : entry.1 ≠ start := by omega
          simpa only [bodySourceFrom, if_neg different] using ih (start + 1) inside

theorem body_extracted_before_fee (fallback : Nat → SourceSlot ActionView) (body : Body)
    (entry : Nat × TransferSource) (inside : entry ∈ bodyOccurrences 0 body.actions) :
    extracted fallback body entry.1 = locate (.bodyAction entry.1) entry.2 := by
  have bounds := body_original_indices 0 body.actions entry inside
  have different : entry.1 ≠ body.actions.length := by omega
  simpa only [extracted, if_neg different] using body_source_extraction 0 fallback body.actions entry inside

theorem fee_extracted_at_full_length (fallback : Nat → SourceSlot ActionView) (body : Body)
    (fee : TransferSource) (present : body.funding = some fee) :
    extracted fallback body body.actions.length = locate .feeFunding fee := by
  simp only [extracted, if_pos rfl, if_true, present]

theorem body_signature_member (actions : List Action) (transfer : TransferSource)
    (inside : Action.transfer transfer ∈ actions) :
    spend transfer ∈ actions.flatMap Action.spends := by
  exact List.mem_flatMap.mpr ⟨Action.transfer transfer, inside, by simp [Action.spends]⟩

theorem every_occurrence_signature (body : Body) (entry : Nat × TransferSource)
    (inside : entry ∈ occurrences body) : spend entry.2 ∈ signatureArguments body := by
  rcases List.mem_append.mp inside with ordinary | fee
  · exact List.mem_append_left _
      (body_signature_member body.actions entry.2 (body_occurrence_source 0 body.actions entry ordinary))
  · obtain ⟨transfer, present, same⟩ := List.mem_map.mp fee
    subst entry
    exact List.mem_append_right _ (List.mem_map.mpr ⟨transfer, present, rfl⟩)

theorem funding_after_full_body (body : Body) (fee : TransferSource)
    (present : body.funding = some fee) :
    occurrences body = bodyOccurrences 0 body.actions ++ [(body.actions.length, fee)] ∧
    (mixedBody body).length = body.actions.length ∧ mixedFee body = some (locate .feeFunding fee) := by
  exact ⟨by simp [occurrences, present],
    mixed_body_length 0 body.actions, by simp [mixedFee, present]⟩

theorem body_projection_order (start : Nat) (actions : List Action) :
    (bodyOccurrences start actions).map (fun entry =>
      (entry.1, (⟨.transfer, locate (.bodyAction entry.1) entry.2⟩ :
        TransferMixedBody.Action (SourceSlot ActionView)))) =
      TransferMixedBody.selected start (mixedFrom start actions) := by
  induction actions generalizing start with
  | nil => rfl
  | cons action rest ih =>
      cases action with
      | transfer transfer =>
          simp [bodyOccurrences, mixedFrom, TransferMixedBody.selected, TransferMixedBody.bodyFrom, ih]
      | sibling sibling =>
          cases kind : sibling.kind <;>
            simp [bodyOccurrences, mixedFrom, SiblingKind.kind, kind, TransferMixedBody.selected,
              TransferMixedBody.bodyFrom, ih]

theorem funding_distinct_from_body (body : Body) (entry : Nat × TransferSource)
    (inside : entry ∈ bodyOccurrences 0 body.actions) : entry.1 ≠ body.actions.length := by
  have bounds := body_original_indices 0 body.actions entry inside
  omega

/-- Enumeration is supplied by the constructor rather than an unrelated
signature callback. The remaining encoder/hash/key callbacks still require
exact native source refinement, and are not trusted as Transfer semantics. -/
def signatureModel (base : TransferFullCarrierAcceptance.Model (NativeTransaction Body) ActionView) :
    TransferFullCarrierAcceptance.Model (NativeTransaction Body) ActionView :=
  { base with spends := fun transaction => signatureArguments transaction.body }

def catalogueModel (base : TransferFullCarrierAcceptance.Model (NativeTransaction Body) ActionView) :
    TransferFullCarrierAcceptance.Model (NativeTransaction Body) ActionView :=
  { signatureModel base with
    slots := fun transaction => (occurrences transaction.body).map Prod.fst
    extract := fun transaction index => extracted (base.extract transaction) transaction.body index }

theorem body_expected_same_source
    (base : TransferFullCarrierAcceptance.Model (NativeTransaction Body) ActionView)
    (decode : List Nat → Option (NativeTransaction Body)) (crypto : TransferSem.Crypto)
    (transaction : NativeTransaction Body) (entry : Nat × TransferSource)
    (inside : entry ∈ bodyOccurrences 0 transaction.body.actions) :
    TransferFullCarrierAcceptance.expected (contextModel (catalogueModel base) decode) crypto 1
      (carrier transaction) entry.1 = TransferNativeMixedJoin.actualItem crypto transaction.anchor
        (locate (.bodyAction entry.1) entry.2) := by
  have source : (catalogueModel base).extract transaction entry.1 =
      locate (.bodyAction entry.1) entry.2 :=
    body_extracted_before_fee (base.extract transaction) transaction.body entry inside
  change sourceItem 1 (fun action => (statement action).fields) (crypto.hash .transferStatement)
    (TransferNativeMixedJoin.checkedSource transaction.anchor ((catalogueModel base).extract transaction entry.1)) = _
  rw [source]
  rfl

theorem fee_expected_same_source
    (base : TransferFullCarrierAcceptance.Model (NativeTransaction Body) ActionView)
    (decode : List Nat → Option (NativeTransaction Body)) (crypto : TransferSem.Crypto)
    (transaction : NativeTransaction Body) (fee : TransferSource) (present : transaction.body.funding = some fee) :
    TransferFullCarrierAcceptance.expected (contextModel (catalogueModel base) decode) crypto 1
      (carrier transaction) transaction.body.actions.length = TransferNativeMixedJoin.actualItem crypto
        transaction.anchor (locate .feeFunding fee) := by
  have source : (catalogueModel base).extract transaction transaction.body.actions.length =
      locate .feeFunding fee :=
    fee_extracted_at_full_length (base.extract transaction) transaction.body fee present
  change sourceItem 1 (fun action => (statement action).fields) (crypto.hash .transferStatement)
    (TransferNativeMixedJoin.checkedSource transaction.anchor
      ((catalogueModel base).extract transaction transaction.body.actions.length)) = _
  rw [source]
  rfl

theorem constructed_occurrence_signature_arguments
    (base : TransferFullCarrierAcceptance.Model (NativeTransaction Body) ActionView)
    (decode : List Nat → Option (NativeTransaction Body)) (crypto : TransferSem.Crypto)
    (input : TransferFullCarrierAcceptance.Inputs) (raw : List Nat)
    (cached : TransferWarmCache.Cached (NativeTransaction Body))
    (made : TransferWarmCache.construct (contextModel (catalogueModel base) decode) crypto
      (transferInputs input) raw = some cached)
    (entry : Nat × TransferSource) (inside : entry ∈ occurrences cached.prepared.carrier.body.body) :
    entry.2.source.body.bodyAnchor = cached.prepared.carrier.anchor ∧ entry.2.key ≠ 0 ∧
    input.verifySpend entry.2.key
      (base.effectHash (base.effectFields cached.prepared.carrier.body)) entry.2.signature = true := by
  have arguments := (TransferNativeMixedJoin.constructed_signature_arguments (catalogueModel base)
    decode crypto input raw cached made).2.2.2
  exact arguments (spend entry.2) (every_occurrence_signature _ entry inside)

set_option pp.all true in
#check @locate_preserves_full_source
#print axioms locate_preserves_full_source
set_option pp.all true in
#check @mixed_body_length
#print axioms mixed_body_length
set_option pp.all true in
#check @body_original_indices
#print axioms body_original_indices
set_option pp.all true in
#check @body_occurrence_source
#print axioms body_occurrence_source
set_option pp.all true in
#check @body_source_extraction
#print axioms body_source_extraction
set_option pp.all true in
#check @body_extracted_before_fee
#print axioms body_extracted_before_fee
set_option pp.all true in
#check @fee_extracted_at_full_length
#print axioms fee_extracted_at_full_length
set_option pp.all true in
#check @body_signature_member
#print axioms body_signature_member
set_option pp.all true in
#check @every_occurrence_signature
#print axioms every_occurrence_signature
set_option pp.all true in
#check @funding_after_full_body
#print axioms funding_after_full_body
set_option pp.all true in
#check @body_projection_order
#print axioms body_projection_order
set_option pp.all true in
#check @funding_distinct_from_body
#print axioms funding_distinct_from_body
set_option pp.all true in
#check @body_expected_same_source
#print axioms body_expected_same_source
set_option pp.all true in
#check @fee_expected_same_source
#print axioms fee_expected_same_source
set_option pp.all true in
#check @constructed_occurrence_signature_arguments
#print axioms constructed_occurrence_signature_arguments

end ShielddSecurity.TransferNativeSourceCatalogue
