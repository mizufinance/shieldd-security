import ShielddSecurity.RuntimeBalanceVariableSequenceSigned
import ShielddSecurity.TransferBalanceFinalFrame
import ShielddSecurity.TransferBalanceGroupRelation
import ShielddSecurity.TransferBalanceBlindingCommittedCompletion

set_option maxHeartbeats 400000
set_option maxRecDepth 4096
namespace ShielddSecurity.TransferBalanceGroupCompletion

variable {F : Type} [Field F] [DecidableEq F] [CharP F Scalar.modulus]
variable {E S R K Q Signing J : Type} [AddCommGroup J]
variable (fq : GroupNativeSdk.FqBytes Q) (fr : GroupNativeSdk.FrBytes R)
variable (model : Group.StandardCurveModel J (RuntimeTransferBalanceFinalAddCompletion.d : F))
variable (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr
  (RuntimeTransferBalanceFinalAddCompletion.d : F) model)
variable {Encoded Native : Type} (backend : ShielddScalarReader.Backend (F := F) Encoded Native)
variable (point : S)

def initialAssignment (base : Nat → F) : Nat → F := fun column =>
  if column = 9 then base 2 else base column

theorem initialized_shadow (base : Nat → F) : initialAssignment base 9 = initialAssignment base 2 := by
  simp only [initialAssignment, if_true, if_neg (by decide : ¬ (2 : Nat) = 9)]

theorem variable_preserves (base : Nat → F) (n column : Nat)
    (kept : column ∈ RuntimeBalanceVariableSequence.kept)
    (outsideBits : column < 21713 ∨ 21842 ≤ column)
    (outsidePrecompute : column ∉ RuntimeBalanceVariableWindow000NativePrecompute.allWrites) :
    RuntimeBalanceVariableSequence.construct fq fr model upstream backend point base n column = base column := by
  have loop := GroupFixedCircuitCompletion.run_preserves
    (RuntimeBalanceVariableSequence.prepared fq fr model upstream backend point base n)
    (RuntimeBalanceVariableSequence.programs n) RuntimeBalanceVariableSequence.kept
    (RuntimeBalanceVariableSequence.protection n) column kept
  have precompute := RuntimeBalanceVariableWindow000NativePrecompute.outside
    fq fr model upstream backend point (writeBits base 21713 (encodeBits 129 n)) column outsidePrecompute
  have bits := writeBits_preserves base 21713 (encodeBits 129 n) column
    (by simpa only [encodeBits_length] using outsideBits)
  exact loop.trans (precompute.trans bits)

def unsigned (base : Nat → F) (amounts : TransferSignedMagnitude.Inputs) : Nat → F :=
  RuntimeBalanceVariableSequence.construct fq fr model upstream backend point
    (RuntimeTransferSignedBalanceCompletion.completeAssignment (initialAssignment base) amounts)
    (TransferSignedMagnitude.magnitude amounts)

def blinded (base : Nat → F) (amounts : TransferSignedMagnitude.Inputs) (b : Nat) : Nat → F :=
  RuntimeBalanceBlindingTemplateCanonicalPreservation.construct
    (unsigned fq fr model upstream backend point base amounts) b

def construct (base : Nat → F) (amounts : TransferSignedMagnitude.Inputs) (b : Nat) : Nat → F :=
  RuntimeTransferBalanceFinalAddCompletion.completeAssignment
    (blinded fq fr model upstream backend point base amounts b)

private theorem signed_difference (amounts : TransferSignedMagnitude.Inputs) :
    (if TransferSignedMagnitude.negative amounts then
      -(TransferSignedMagnitude.magnitude amounts : Int) else
      (TransferSignedMagnitude.magnitude amounts : Int)) =
    (TransferSignedMagnitude.inputTotal amounts : Int) -
      (TransferSignedMagnitude.outputTotal amounts : Int) := by
  by_cases less : TransferSignedMagnitude.inputTotal amounts < TransferSignedMagnitude.outputTotal amounts
  · simp only [TransferSignedMagnitude.negative, TransferSignedMagnitude.magnitude,
      less, decide_true, if_true]
    omega
  · simp only [TransferSignedMagnitude.negative, TransferSignedMagnitude.magnitude,
      less, decide_false, Bool.false_eq_true, if_false]
    omega

/-- Legal bounded amounts and canonical blinding construct the entire captured
balance relation. Shadow9 is initialized from committed2. Each later constructor
preserves the actual earlier rows; the desired endpoint is a conclusion. -/
theorem complete (base : Nat → F) (amounts : TransferSignedMagnitude.Inputs) (b : Nat)
    (canonical : b < Scalar.order) (committed : base 2 = (b : F))
    (one : base 0 = 1) (linked : base 200692 = base 0)
    (nativeAmounts : ∀ i, base (RuntimeTransferSignedBalanceCompletion.amountColumns i) = ((amounts i).val : F))
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeTransferBalanceFinalAddCompletion.d : F))
    (imaginarySquare : imaginary * imaginary = -1) (blindingBase : J)
    (blindingMeaning : (RuntimeBalanceBlindingWindow000.base : Group.Point F) = model.coordinates blindingBase) :
    Satisfies (construct fq fr model upstream backend point base amounts b) TransferBalanceGroupRelation.rows ∧
      RuntimeTransferBalanceFinalAddCompletion.outputPoint
        (construct fq fr model upstream backend point base amounts b) = model.coordinates
        (((TransferSignedMagnitude.inputTotal amounts : Int) -
          (TransferSignedMagnitude.outputTotal amounts : Int)) •
            (upstream.embed (upstream.promote point)) + b • blindingBase) := by
  let n := TransferSignedMagnitude.magnitude amounts
  let signed := RuntimeTransferSignedBalanceCompletion.completeAssignment (initialAssignment base) amounts
  let u := unsigned fq fr model upstream backend point base amounts
  let h := blinded fq fr model upstream backend point base amounts b
  have initOne : initialAssignment base 0 = 1 := by simpa only [initialAssignment, if_neg (by decide : ¬ (0 : Nat) = 9)] using one
  have initLink : initialAssignment base 200692 = initialAssignment base 0 := by
    simpa only [initialAssignment, if_neg (by decide : ¬ (200692 : Nat) = 9),
      if_neg (by decide : ¬ (0 : Nat) = 9)] using linked
  have initAmounts : ∀ i, initialAssignment base (RuntimeTransferSignedBalanceCompletion.amountColumns i) = ((amounts i).val : F) := by
    intro i
    have unchanged : RuntimeTransferSignedBalanceCompletion.amountColumns i ≠ 9 :=
      (by decide : ∀ j : Fin 4, RuntimeTransferSignedBalanceCompletion.amountColumns j ≠ 9) i
    simpa only [initialAssignment, if_neg unchanged] using nativeAmounts i
  have built := RuntimeBalanceVariableSequence.constructs_from_signed fq fr model upstream backend point
    (initialAssignment base) amounts initOne initLink initAmounts imaginary nonSquare imaginarySquare
  have keptSmall (column : Nat) (selected : column = 0 ∨ column = 2 ∨ column = 9 ∨ column = 200692) : u column = initialAssignment base column := by
    have variableSame : u column = signed column := by
      apply variable_preserves fq fr model upstream backend point signed n column
      all_goals rcases selected with rfl | rfl | rfl | rfl <;> decide
    exact variableSame.trans (RuntimeTransferSignedBalanceCompletion.preserves (initialAssignment base) amounts column
      (by rcases selected with rfl | rfl | rfl | rfl <;> decide))
  have uOne : u 0 = 1 := (keptSmall 0 (Or.inl rfl)).trans initOne
  have uLink : u 200692 = u 0 := by
    rw [keptSmall 200692 (Or.inr (Or.inr (Or.inr rfl))), keptSmall 0 (Or.inl rfl), initLink]
  have uCommitted : u 2 = (b : F) := by
    rw [keptSmall 2 (Or.inr (Or.inl rfl))]
    simpa only [initialAssignment, if_neg (by decide : ¬ (2 : Nat) = 9)] using committed
  have uShadow : u 9 = u 2 := by
    rw [keptSmall 9 (Or.inr (Or.inr (Or.inl rfl))), keptSmall 2 (Or.inr (Or.inl rfl))]
    exact initialized_shadow base
  have hBuilt := TransferBalanceBlindingCommittedCompletion.complete model u b blindingBase canonical
    uCommitted uShadow uOne uLink four imaginary nonSquare imaginarySquare blindingMeaning
  have previous := TransferBalanceVariableFrame.h_preserves u n b built.1
  have hOne : h 0 = 1 := (RuntimeBalanceBlindingTemplateFrameBounds.preserves_covered u b 0 (by decide)).trans uOne
  have hLink : h 200692 = h 0 := by
    change RuntimeBalanceBlindingTemplateCanonicalPreservation.construct u b 200692 =
      RuntimeBalanceBlindingTemplateCanonicalPreservation.construct u b 0
    rw [RuntimeBalanceBlindingTemplateFrameBounds.preserves_covered u b 200692 (by decide),
      RuntimeBalanceBlindingTemplateFrameBounds.preserves_covered u b 0 (by decide), uLink]
  have uPoint : RuntimeTransferBalanceFinalAddCompletion.unsignedPoint u =
      model.coordinates (n • (upstream.embed (upstream.promote point))) := by
    rw [TransferBalanceGroupRelation.unsigned_input]
    rw [← RuntimeBalanceVariableSequenceSoundness.output_identity u n]
    exact built.2
  have hUnsigned : RuntimeTransferBalanceFinalAddCompletion.unsignedPoint h =
      RuntimeTransferBalanceFinalAddCompletion.unsignedPoint u := by
    apply congrArg₂ Group.Point.mk
    · simpa only [RuntimeTransferBalanceFinalAddCompletion.unsignedX, eval, Int.cast_one,
        one_mul, add_zero] using RuntimeBalanceBlindingTemplateFrameBounds.preserves_covered u b 22230 (by decide)
    · simpa only [RuntimeTransferBalanceFinalAddCompletion.unsignedY, eval, Int.cast_one,
        one_mul, add_zero] using RuntimeBalanceBlindingTemplateFrameBounds.preserves_covered u b 22231 (by decide)
  have hBlinded : RuntimeTransferBalanceFinalAddCompletion.blindedPoint h = model.coordinates (b • blindingBase) :=
    (TransferBalanceGroupRelation.blinding_input h).symm.trans hBuilt.2
  have negative : eval h RuntimeTransferBalanceFinalAddCompletion.negative =
      if TransferSignedMagnitude.negative amounts then 1 else 0 := by
    have uNegative : u 21711 = signed 21711 :=
      variable_preserves fq fr model upstream backend point signed n 21711 (by decide) (by decide) (by decide)
    have hNegative := RuntimeBalanceBlindingTemplateFrameBounds.preserves_covered u b 21711 (by decide)
    simp only [RuntimeTransferBalanceFinalAddCompletion.negative, eval, Int.cast_one, one_mul, add_zero]
    exact hNegative.trans (uNegative.trans (RuntimeTransferSignedBalanceCompletion.final_negative (initialAssignment base) amounts))
  have unsignedCurved : Group.OnCurve (RuntimeTransferBalanceFinalAddCompletion.d : F)
      (RuntimeTransferBalanceFinalAddCompletion.unsignedPoint h) := by
    rw [hUnsigned, uPoint]
    exact model.onCurve _
  have blindingCurved : Group.OnCurve (RuntimeTransferBalanceFinalAddCompletion.d : F)
      (RuntimeTransferBalanceFinalAddCompletion.blindedPoint h) := by
    rw [hBlinded]
    exact model.onCurve _
  have finalBuilt := RuntimeTransferBalanceFinalAddCompletion.actual_rows_complete h hOne hLink imaginary
    nonSquare imaginarySquare (TransferSignedMagnitude.negative amounts) negative
    unsignedCurved blindingCurved
  have prior : Satisfies h (TransferBalanceFinalFrame.priorRows n) := by
    intro row member
    rcases List.mem_append.mp member with earlier | remaining
    · exact previous row (List.mem_append_left _ earlier)
    · rcases List.mem_append.mp remaining with windowRows | fixedRows
      · exact previous row (List.mem_append_right _ windowRows)
      · exact hBuilt.1 row fixedRows
  have retained := TransferBalanceFinalFrame.preserves_prior h n prior
  constructor
  · change Satisfies _ (RuntimeTransferSignedBalanceCompletion.rawRows ++
      (RuntimeBalanceVariableSequence.ownedRows 0 ++
        (TransferBalanceBlindingCommittedRelation.rows ++ RuntimeTransferBalanceFinalAddCompletion.rawRows)))
    rw [← RuntimeBalanceVariableSequenceSoundness.row_identity n]
    intro row member
    have grouped : row ∈ TransferBalanceFinalFrame.priorRows n ++ RuntimeTransferBalanceFinalAddCompletion.rawRows := by
      simpa only [TransferBalanceFinalFrame.priorRows, List.append_assoc] using member
    rcases List.mem_append.mp grouped with earlier | finalRows
    · exact retained row earlier
    · exact finalBuilt.1 row finalRows
  · have endpoint := finalBuilt.2
    rw [hUnsigned, uPoint, hBlinded] at endpoint
    have native := GroupSignedPoint.final_native (RuntimeTransferBalanceFinalAddCompletion.d : F)
      imaginary model nonSquare imaginarySquare (TransferSignedMagnitude.negative amounts)
      (n • (upstream.embed (upstream.promote point))) (b • blindingBase)
    have signedMeaning : (if TransferSignedMagnitude.negative amounts then
        -(n • (upstream.embed (upstream.promote point))) else
        n • (upstream.embed (upstream.promote point))) =
        ((TransferSignedMagnitude.inputTotal amounts : Int) -
          (TransferSignedMagnitude.outputTotal amounts : Int)) •
            (upstream.embed (upstream.promote point)) := by
      rw [← signed_difference amounts]
      cases TransferSignedMagnitude.negative amounts <;>
        simp only [Bool.false_eq_true, if_false, if_true, neg_zsmul, natCast_zsmul, n]
    exact endpoint.trans (native.trans (congrArg model.coordinates (congrArg (fun left => left + b • blindingBase) signedMeaning)))

set_option pp.all true in
#check @initialized_shadow
#print axioms initialized_shadow
set_option pp.all true in
#check @variable_preserves
#print axioms variable_preserves
set_option pp.all true in
#check @complete
#print axioms complete
end ShielddSecurity.TransferBalanceGroupCompletion
