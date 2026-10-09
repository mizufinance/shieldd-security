import ShielddSecurity.TransferCommittedBlindingRangeBridge
import ShielddSecurity.TransferFieldClaimAcceptance

set_option maxHeartbeats 300000

namespace ShielddSecurity.TransferOwnedRangeInclusion

/-! Original row indices are preserved block by block. The indexed coverage
certificate is a concrete, separately checkable full-capture obligation; it is
not inferred from a digest or local slice. The semantic/admission consequence
still requires the unchanged independent full LocalRowSoundness contract. -/

def committedLc : Linear := [(2, 1)]

theorem field_moduli_match : TransferCore.fieldModulus = Scalar.modulus := rfl

theorem subgroup_orders_match : TransferCore.scalarOrder = Scalar.order := rfl

theorem c0_projection :
    (RuntimeBalanceBlindingCanonical.c0OriginalIndices.zip RuntimeBalanceBlindingCanonical.c0Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c0Raw :=
  List.map_snd_zip (by decide)

theorem c1_projection :
    (RuntimeBalanceBlindingCanonical.c1OriginalIndices.zip RuntimeBalanceBlindingCanonical.c1Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c1Raw :=
  List.map_snd_zip (by decide)

theorem c2_projection :
    (RuntimeBalanceBlindingCanonical.c2OriginalIndices.zip RuntimeBalanceBlindingCanonical.c2Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c2Raw :=
  List.map_snd_zip (by decide)

theorem c3_projection :
    (RuntimeBalanceBlindingCanonical.c3OriginalIndices.zip RuntimeBalanceBlindingCanonical.c3Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c3Raw :=
  List.map_snd_zip (by decide)

theorem c4_projection :
    (RuntimeBalanceBlindingCanonical.c4OriginalIndices.zip RuntimeBalanceBlindingCanonical.c4Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c4Raw :=
  List.map_snd_zip (by decide)

theorem c5_projection :
    (RuntimeBalanceBlindingCanonical.c5OriginalIndices.zip RuntimeBalanceBlindingCanonical.c5Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c5Raw :=
  List.map_snd_zip (by decide)

theorem c6_projection :
    (RuntimeBalanceBlindingCanonical.c6OriginalIndices.zip RuntimeBalanceBlindingCanonical.c6Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c6Raw :=
  List.map_snd_zip (by decide)

theorem c7_projection :
    (RuntimeBalanceBlindingCanonical.c7OriginalIndices.zip RuntimeBalanceBlindingCanonical.c7Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c7Raw :=
  List.map_snd_zip (by decide)

theorem c8_projection :
    (RuntimeBalanceBlindingCanonical.c8OriginalIndices.zip RuntimeBalanceBlindingCanonical.c8Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c8Raw :=
  List.map_snd_zip (by decide)

theorem c9_projection :
    (RuntimeBalanceBlindingCanonical.c9OriginalIndices.zip RuntimeBalanceBlindingCanonical.c9Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c9Raw :=
  List.map_snd_zip (by decide)

theorem c10_projection :
    (RuntimeBalanceBlindingCanonical.c10OriginalIndices.zip RuntimeBalanceBlindingCanonical.c10Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c10Raw :=
  List.map_snd_zip (by decide)

theorem c11_projection :
    (RuntimeBalanceBlindingCanonical.c11OriginalIndices.zip RuntimeBalanceBlindingCanonical.c11Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c11Raw :=
  List.map_snd_zip (by decide)

theorem c12_projection :
    (RuntimeBalanceBlindingCanonical.c12OriginalIndices.zip RuntimeBalanceBlindingCanonical.c12Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c12Raw :=
  List.map_snd_zip (by decide)

theorem c13_projection :
    (RuntimeBalanceBlindingCanonical.c13OriginalIndices.zip RuntimeBalanceBlindingCanonical.c13Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c13Raw :=
  List.map_snd_zip (by decide)

theorem c14_projection :
    (RuntimeBalanceBlindingCanonical.c14OriginalIndices.zip RuntimeBalanceBlindingCanonical.c14Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c14Raw :=
  List.map_snd_zip (by decide)

theorem c15_projection :
    (RuntimeBalanceBlindingCanonical.c15OriginalIndices.zip RuntimeBalanceBlindingCanonical.c15Raw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.c15Raw :=
  List.map_snd_zip (by decide)

theorem tail_projection :
    (RuntimeBalanceBlindingCanonical.tailOriginalIndices.zip RuntimeBalanceBlindingCanonical.tailRaw).map Prod.snd =
      RuntimeBalanceBlindingCanonical.tailRaw :=
  List.map_snd_zip (by decide)

def indexedBlocks : List (List (Nat × Row)) :=
  [[(200768, ⟨[(2, 1), (9, (Scalar.modulus - 1 : Nat))], []⟩)],
    RuntimeBalanceBlindingCanonical.c0OriginalIndices.zip RuntimeBalanceBlindingCanonical.c0Raw,
    RuntimeBalanceBlindingCanonical.c1OriginalIndices.zip RuntimeBalanceBlindingCanonical.c1Raw,
    RuntimeBalanceBlindingCanonical.c2OriginalIndices.zip RuntimeBalanceBlindingCanonical.c2Raw,
    RuntimeBalanceBlindingCanonical.c3OriginalIndices.zip RuntimeBalanceBlindingCanonical.c3Raw,
    RuntimeBalanceBlindingCanonical.c4OriginalIndices.zip RuntimeBalanceBlindingCanonical.c4Raw,
    RuntimeBalanceBlindingCanonical.c5OriginalIndices.zip RuntimeBalanceBlindingCanonical.c5Raw,
    RuntimeBalanceBlindingCanonical.c6OriginalIndices.zip RuntimeBalanceBlindingCanonical.c6Raw,
    RuntimeBalanceBlindingCanonical.c7OriginalIndices.zip RuntimeBalanceBlindingCanonical.c7Raw,
    RuntimeBalanceBlindingCanonical.c8OriginalIndices.zip RuntimeBalanceBlindingCanonical.c8Raw,
    RuntimeBalanceBlindingCanonical.c9OriginalIndices.zip RuntimeBalanceBlindingCanonical.c9Raw,
    RuntimeBalanceBlindingCanonical.c10OriginalIndices.zip RuntimeBalanceBlindingCanonical.c10Raw,
    RuntimeBalanceBlindingCanonical.c11OriginalIndices.zip RuntimeBalanceBlindingCanonical.c11Raw,
    RuntimeBalanceBlindingCanonical.c12OriginalIndices.zip RuntimeBalanceBlindingCanonical.c12Raw,
    RuntimeBalanceBlindingCanonical.c13OriginalIndices.zip RuntimeBalanceBlindingCanonical.c13Raw,
    RuntimeBalanceBlindingCanonical.c14OriginalIndices.zip RuntimeBalanceBlindingCanonical.c14Raw,
    RuntimeBalanceBlindingCanonical.c15OriginalIndices.zip RuntimeBalanceBlindingCanonical.c15Raw,
    RuntimeBalanceBlindingCanonical.tailOriginalIndices.zip RuntimeBalanceBlindingCanonical.tailRaw]

def indexedOwnedRows : List (Nat × Row) := indexedBlocks.flatten

theorem owned_bodies : indexedOwnedRows.map Prod.snd =
    TransferCommittedBlindingRangeBridge.localRows := by
  simp only [indexedOwnedRows, indexedBlocks, List.map_append, List.map_cons, List.map_nil,
    c0_projection, c1_projection, c2_projection, c3_projection, c4_projection, c5_projection, c6_projection, c7_projection, c8_projection, c9_projection, c10_projection, c11_projection, c12_projection, c13_projection, c14_projection, c15_projection, tail_projection,
    TransferCommittedBlindingRangeBridge.localRows, TransferCommittedBlindingRangeBridge.inputRows,
    RuntimeBalanceBlindingCanonical.originalRows, RuntimeBalanceBlindingCanonical.originalBlocks,
    List.flatten_cons, List.flatten_nil]

/-- Every original index has the exact body in the complete stored-row list. -/
def IndexedCoverage (fullRows : List Row) : Prop :=
  ∀ entry ∈ indexedOwnedRows, fullRows[entry.1]? = some entry.2

/-- Executable bounded row-body certificate. A later exact indexed full representation
must supply an actual true result; none is fabricated from identity metadata here. -/
def checkIndexedCoverage (rowAt : Nat → Option Row) : Bool :=
  indexedOwnedRows.all fun entry => decide (rowAt entry.1 = some entry.2)

theorem checked_indexed_coverage (fullRows : List Row)
    (checked : checkIndexedCoverage (fun index => fullRows[index]?) = true) :
    IndexedCoverage fullRows := by
  intro entry member
  exact of_decide_eq_true ((List.all_eq_true.mp checked) entry member)

theorem inclusion_from_indexed_coverage (fullRows : List Row)
    (coverage : IndexedCoverage fullRows) :
    TransferCommittedBlindingRangeBridge.FullRowInclusion fullRows := by
  intro row member
  have inside : row ∈ indexedOwnedRows.map Prod.snd := by
    simpa only [owned_bodies] using member
  obtain ⟨entry, present, equal⟩ := List.mem_map.mp inside
  have found : entry.2 ∈ fullRows := List.mem_iff_getElem?.mpr ⟨entry.1, coverage entry present⟩
  exact equal ▸ found

variable {F : Type} [Field F] [CharP F TransferCore.fieldModulus]

/-- The desired range premise is proved from the owned rows, not assumed as upstream knowledge. -/
theorem concrete_owned_range (codec : TransferReduction.CanonicalField F) (fullRows : List Row)
    (inclusion : TransferCommittedBlindingRangeBridge.FullRowInclusion fullRows) :
    TransferFieldClaimAcceptance.OwnedRange codec fullRows committedLc := by
  intro rho one satisfied
  have bound := TransferCommittedBlindingRangeBridge.full_decoded_bound
    fullRows inclusion codec rho one satisfied
  simpa only [TransferFieldClaimAcceptance.OwnedRange, committedLc, eval,
    Int.cast_one, one_mul, add_zero, subgroup_orders_match] using bound

theorem indexed_owned_range (codec : TransferReduction.CanonicalField F) (fullRows : List Row)
    (coverage : IndexedCoverage fullRows) :
    TransferFieldClaimAcceptance.OwnedRange codec fullRows committedLc :=
  concrete_owned_range codec fullRows (inclusion_from_indexed_coverage fullRows coverage)

theorem checked_owned_range (codec : TransferReduction.CanonicalField F) (fullRows : List Row)
    (checked : checkIndexedCoverage (fun index => fullRows[index]?) = true) :
    TransferFieldClaimAcceptance.OwnedRange codec fullRows committedLc :=
  indexed_owned_range codec fullRows (checked_indexed_coverage fullRows checked)

theorem preparation_semantic_from_indexed_range {T B : Type}
    (model : TransferFullCarrierAcceptance.Model T B) (crypto : TransferSem.Crypto)
    (canonical : TransferSem.CanonicalCrypto crypto) (input : TransferFullCarrierAcceptance.Inputs)
    (environment : TransferFullCarrierAcceptance.Environment)
    (codec : TransferReduction.CanonicalField F) (fullRows : List Row) (publicLc : Linear)
    (coverage : IndexedCoverage fullRows) (opensField : List Nat → F → Prop)
    (knowledge : TransferFieldClaimAcceptance.UpstreamFieldKnowledge input fullRows publicLc committedLc opensField)
    (soundness : TransferFullCarrierAcceptance.LocalRowSoundness (F := F) crypto fullRows publicLc
      committedLc (TransferFieldClaimAcceptance.naturalOpening opensField))
    (raw : List Nat) (prepared : TransferFullCarrierAcceptance.Prepared T)
    (success : TransferFullCarrierAcceptance.prepare model crypto input environment raw = some prepared) :
    ∀ index ∈ model.slots prepared.carrier.body,
      TransferFullCarrierAcceptance.SemanticOrCollision model crypto (model.extract prepared.carrier.body index) :=
  TransferFieldClaimAcceptance.preparation_semantic_or_collision_from_field_knowledge
    model crypto canonical input environment codec fullRows publicLc committedLc opensField knowledge
    (indexed_owned_range codec fullRows coverage) soundness raw prepared success

theorem consequence_from_indexed_range {T B : Type}
    (model : TransferFullCarrierAcceptance.Model T B) (crypto : TransferSem.Crypto)
    (canonical : TransferSem.CanonicalCrypto crypto) (input : TransferFullCarrierAcceptance.Inputs)
    (environment : TransferFullCarrierAcceptance.Environment)
    (codec : TransferReduction.CanonicalField F) (fullRows : List Row) (publicLc : Linear)
    (coverage : IndexedCoverage fullRows) (opensField : List Nat → F → Prop)
    (knowledge : TransferFieldClaimAcceptance.UpstreamFieldKnowledge input fullRows publicLc committedLc opensField)
    (soundness : TransferFullCarrierAcceptance.LocalRowSoundness (F := F) crypto fullRows publicLc
      committedLc (TransferFieldClaimAcceptance.naturalOpening opensField))
    (mode : TransferIndexing.Mode) (state after : TransferIndexing.State)
    (transaction : Nat) (raw : List Nat) (prepared : TransferFullCarrierAcceptance.Prepared T)
    (success : TransferFullCarrierAcceptance.run model crypto input environment mode state transaction raw =
      some (prepared, after)) :
    TransferFullCarrierAcceptance.Consequence model crypto input environment mode state after transaction raw prepared :=
  TransferFieldClaimAcceptance.full_carrier_consequence_from_field_knowledge
    model crypto canonical input environment codec fullRows publicLc committedLc opensField knowledge
    (indexed_owned_range codec fullRows coverage) soundness mode state after transaction raw prepared success

set_option pp.all true in
#check @field_moduli_match
#print axioms field_moduli_match
set_option pp.all true in
#check @subgroup_orders_match
#print axioms subgroup_orders_match
set_option pp.all true in
#check @c0_projection
#print axioms c0_projection
set_option pp.all true in
#check @c1_projection
#print axioms c1_projection
set_option pp.all true in
#check @c2_projection
#print axioms c2_projection
set_option pp.all true in
#check @c3_projection
#print axioms c3_projection
set_option pp.all true in
#check @c4_projection
#print axioms c4_projection
set_option pp.all true in
#check @c5_projection
#print axioms c5_projection
set_option pp.all true in
#check @c6_projection
#print axioms c6_projection
set_option pp.all true in
#check @c7_projection
#print axioms c7_projection
set_option pp.all true in
#check @c8_projection
#print axioms c8_projection
set_option pp.all true in
#check @c9_projection
#print axioms c9_projection
set_option pp.all true in
#check @c10_projection
#print axioms c10_projection
set_option pp.all true in
#check @c11_projection
#print axioms c11_projection
set_option pp.all true in
#check @c12_projection
#print axioms c12_projection
set_option pp.all true in
#check @c13_projection
#print axioms c13_projection
set_option pp.all true in
#check @c14_projection
#print axioms c14_projection
set_option pp.all true in
#check @c15_projection
#print axioms c15_projection
set_option pp.all true in
#check @tail_projection
#print axioms tail_projection
set_option pp.all true in
#check @owned_bodies
#print axioms owned_bodies
set_option pp.all true in
#check @checked_indexed_coverage
#print axioms checked_indexed_coverage
set_option pp.all true in
#check @inclusion_from_indexed_coverage
#print axioms inclusion_from_indexed_coverage
set_option pp.all true in
#check @concrete_owned_range
#print axioms concrete_owned_range
set_option pp.all true in
#check @indexed_owned_range
#print axioms indexed_owned_range
set_option pp.all true in
#check @checked_owned_range
#print axioms checked_owned_range
set_option pp.all true in
#check @preparation_semantic_from_indexed_range
#print axioms preparation_semantic_from_indexed_range
set_option pp.all true in
#check @consequence_from_indexed_range
#print axioms consequence_from_indexed_range

end ShielddSecurity.TransferOwnedRangeInclusion
