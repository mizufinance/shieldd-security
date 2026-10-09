import ShielddSecurity.RuntimeOwnershipRowPrograms
import ShielddSecurity.RuntimeOwnershipWindow000Point0Soundness
import ShielddSecurity.RuntimeOwnershipWindow000Point1Soundness

set_option maxHeartbeats 300000

namespace ShielddSecurity.OwnershipArbitraryTables


variable {F : Type} [Field F] [CharP F RuntimeOwnershipWindow000Point0Completion.modulus]

def rawRows : List Row := RuntimeOwnershipWindow000Point0Soundness.rawRows ++ RuntimeOwnershipWindow000Point1Soundness.rawRows

theorem base_source (rho : Nat → F) : RuntimeOwnershipWindow000Point0Completion.inputPoint rho = RuntimeOwnershipWindow000Point4SelectorSoundness.basePoint rho := rfl

theorem later_input_source (rho : Nat → F) : RuntimeOwnershipWindow000Point1Completion.inputPoint rho = RuntimeOwnershipWindow000Point4SelectorSoundness.twicePoint rho := rfl

theorem right_source (rho : Nat → F) : RuntimeOwnershipWindow000Point1Completion.rightPoint rho = RuntimeOwnershipWindow000Point4SelectorSoundness.basePoint rho := rfl

theorem twice_source (rho : Nat → F) : RuntimeOwnershipWindow000Point4SelectorSoundness.twicePoint rho = RuntimeOwnershipWindow000Point0Completion.outputPoint rho := by
  simp only [RuntimeOwnershipWindow000Point4SelectorSoundness.twicePoint, RuntimeOwnershipWindow000Point4SelectorSoundness.twiceX, RuntimeOwnershipWindow000Point4SelectorSoundness.twiceY, RuntimeOwnershipWindow000Point0Completion.outputPoint,
    GroupQuotientPairCompletion.point, RuntimeOwnershipWindow000Point0Completion.x, RuntimeOwnershipWindow000Point0Completion.y, eval, Int.cast_one, one_mul, add_zero]

theorem triple_source (rho : Nat → F) : RuntimeOwnershipWindow000Point4SelectorSoundness.triplePoint rho = RuntimeOwnershipWindow000Point1Completion.outputPoint rho := by
  simp only [RuntimeOwnershipWindow000Point4SelectorSoundness.triplePoint, RuntimeOwnershipWindow000Point4SelectorSoundness.tripleX, RuntimeOwnershipWindow000Point4SelectorSoundness.tripleY, RuntimeOwnershipWindow000Point1Completion.outputPoint,
    GroupQuotientPairCompletion.point, RuntimeOwnershipWindow000Point1Completion.x, RuntimeOwnershipWindow000Point1Completion.y, eval, Int.cast_one, one_mul, add_zero]

/-- Only the input operand's native coordinate association is assumed. The
actual arbitrary precompute rows supply both derived table meanings. The
owned sender reader/caller must instantiate the input association separately. -/
theorem actual_native_tables {J : Type} [AddCommGroup J]
    (model : Group.StandardCurveModel J (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (base : J) (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : RuntimeOwnershipWindow000Point4SelectorSoundness.basePoint rho = model.coordinates base)
    (satisfied : Satisfies rho rawRows) :
    RuntimeOwnershipWindow000Point4SelectorSoundness.twicePoint rho = model.coordinates (2 • base) ∧
      RuntimeOwnershipWindow000Point4SelectorSoundness.triplePoint rho = model.coordinates (3 • base) := by
  have firstRows : Satisfies rho RuntimeOwnershipWindow000Point0Soundness.rawRows := by
    intro row member
    exact satisfied row (List.mem_append_left _ member)
  have secondRows : Satisfies rho RuntimeOwnershipWindow000Point1Soundness.rawRows := by
    intro row member
    exact satisfied row (List.mem_append_right _ member)
  have baseCurve : Group.OnCurve (RuntimeOwnershipWindow000Point0Cones.coefficientD : F)
      (RuntimeOwnershipWindow000Point4SelectorSoundness.basePoint rho) := by
    rw [baseMeaning]
    exact model.onCurve base
  have first := RuntimeOwnershipWindow000Point0Soundness.actual_point_sound rho one four imaginary nonSquare imaginarySquare
    (by rw [base_source]; exact baseCurve) firstRows
  have twiceMeaning : RuntimeOwnershipWindow000Point4SelectorSoundness.twicePoint rho = model.coordinates (2 • base) := by
    rw [twice_source, first.1, base_source, baseMeaning, ← model.addition, ← two_nsmul]
  have twiceCurve : Group.OnCurve (RuntimeOwnershipWindow000Point1Cones.coefficientD : F)
      (RuntimeOwnershipWindow000Point1Completion.inputPoint rho) := by
    rw [later_input_source, twiceMeaning]
    exact model.onCurve (2 • base)
  have second := RuntimeOwnershipWindow000Point1Soundness.actual_point_sound rho one four imaginary nonSquare imaginarySquare
    twiceCurve (by rw [right_source]; exact baseCurve) secondRows
  refine ⟨twiceMeaning, ?_⟩
  rw [triple_source, second, later_input_source, right_source, twiceMeaning,
    baseMeaning]
  change Group.affineAdd (RuntimeOwnershipWindow000Point0Cones.coefficientD : F)
    (model.coordinates (2 • base)) (model.coordinates base) = model.coordinates (3 • base)
  rw [← model.addition]
  congr 1
  change 2 • base + base = (2 + 1) • base
  rw [add_nsmul, one_nsmul]

theorem tables_curved {J : Type} [AddCommGroup J]
    (model : Group.StandardCurveModel J (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (base : J) (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (baseMeaning : RuntimeOwnershipWindow000Point4SelectorSoundness.basePoint rho = model.coordinates base)
    (satisfied : Satisfies rho rawRows) :
    GroupVariableCircuitCompletion.Curved
      (RuntimeOwnershipWindow000Point0Cones.coefficientD : F)
      RuntimeOwnershipRowPrograms.firstTables rho := by
  obtain ⟨twiceMeaning, tripleMeaning⟩ := actual_native_tables model base rho one four
    imaginary nonSquare imaginarySquare baseMeaning satisfied
  change Group.OnCurve (RuntimeOwnershipWindow000Point0Cones.coefficientD : F) (RuntimeOwnershipWindow000Point4SelectorSoundness.basePoint rho) ∧
    Group.OnCurve (RuntimeOwnershipWindow000Point0Cones.coefficientD : F) (RuntimeOwnershipWindow000Point4SelectorSoundness.twicePoint rho) ∧
    Group.OnCurve (RuntimeOwnershipWindow000Point0Cones.coefficientD : F) (RuntimeOwnershipWindow000Point4SelectorSoundness.triplePoint rho)
  rw [baseMeaning, twiceMeaning, tripleMeaning]
  exact ⟨model.onCurve base, model.onCurve (2 • base), model.onCurve (3 • base)⟩

set_option pp.all true in
#check @base_source
#print axioms base_source
set_option pp.all true in
#check @later_input_source
#print axioms later_input_source
set_option pp.all true in
#check @right_source
#print axioms right_source
set_option pp.all true in
#check @twice_source
#print axioms twice_source
set_option pp.all true in
#check @triple_source
#print axioms triple_source
set_option pp.all true in
#check @actual_native_tables
#print axioms actual_native_tables
set_option pp.all true in
#check @tables_curved
#print axioms tables_curved

end ShielddSecurity.OwnershipArbitraryTables
