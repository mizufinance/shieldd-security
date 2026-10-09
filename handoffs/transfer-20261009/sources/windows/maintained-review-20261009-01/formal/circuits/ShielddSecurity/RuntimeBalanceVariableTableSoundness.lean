import ShielddSecurity.RuntimeBalanceVariableWindow000Point0Soundness
import ShielddSecurity.RuntimeBalanceVariableWindow000Point1Soundness
import ShielddSecurity.RuntimeBalanceVariableWindow000Program

set_option maxHeartbeats 200000
namespace ShielddSecurity.RuntimeBalanceVariableTableSoundness

def rawRows : List Row := RuntimeBalanceVariableWindow000Point0Soundness.rawRows ++
  RuntimeBalanceVariableWindow000Point1Soundness.rawRows

theorem addition_input {F : Type} [Field F] (rho : Nat → F) :
    RuntimeBalanceVariableWindow000Point1Completion.inputPoint rho =
      RuntimeBalanceVariableWindow000Point0Completion.outputPoint rho := by
  simp only [RuntimeBalanceVariableWindow000Point1Completion.inputPoint,
    RuntimeBalanceVariableWindow000Point1Completion.inputX,RuntimeBalanceVariableWindow000Point1Completion.inputY,
    RuntimeBalanceVariableWindow000Point0Completion.outputPoint,GroupQuotientPairCompletion.point,
    RuntimeBalanceVariableWindow000Point0Completion.x,RuntimeBalanceVariableWindow000Point0Completion.y,
    eval,Int.cast_one,one_mul,add_zero]

theorem addition_base {F : Type} [Field F] (rho : Nat → F) :
    RuntimeBalanceVariableWindow000Point1Completion.rightPoint rho =
      RuntimeBalanceVariableWindow000Point0Completion.inputPoint rho := rfl

/-- The source/native meaning of the actual seed coordinates is explicit.
The two other table meanings are derived from rows on this same assignment. -/
theorem native_tables {F J : Type} [Field F] [AddCommGroup J]
    [CharP F RuntimeBalanceVariableWindow000Point0Completion.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (RuntimeBalanceVariableWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary * imaginary = -1)
    (model : Group.StandardCurveModel J (RuntimeBalanceVariableWindow000Point0Cones.coefficientD : F))
    (base : J)
    (baseMeaning : RuntimeBalanceVariableWindow000Point0Completion.inputPoint rho = model.coordinates base)
    (satisfied : Satisfies rho rawRows) :
    GroupFixedCircuitCompletion.point rho RuntimeBalanceVariableWindow000Program.tables.base = model.coordinates base ∧
    GroupFixedCircuitCompletion.point rho RuntimeBalanceVariableWindow000Program.tables.twice = model.coordinates (2 • base) ∧
    GroupFixedCircuitCompletion.point rho RuntimeBalanceVariableWindow000Program.tables.triple = model.coordinates (3 • base) := by
  have firstRows : Satisfies rho RuntimeBalanceVariableWindow000Point0Soundness.rawRows := by
    intro row member; exact satisfied row (List.mem_append_left _ member)
  have secondRows : Satisfies rho RuntimeBalanceVariableWindow000Point1Soundness.rawRows := by
    intro row member; exact satisfied row (List.mem_append_right _ member)
  have baseCurve : Group.OnCurve (RuntimeBalanceVariableWindow000Point0Cones.coefficientD : F)
      (RuntimeBalanceVariableWindow000Point0Completion.inputPoint rho) := by
    rw [baseMeaning]; exact model.onCurve base
  have first := RuntimeBalanceVariableWindow000Point0Soundness.actual_point_sound rho one four imaginary
    nonSquare imaginarySquare baseCurve firstRows
  have twiceMeaning : RuntimeBalanceVariableWindow000Point0Completion.outputPoint rho = model.coordinates (2 • base) := by
    rw [first.1,baseMeaning,← model.addition,two_nsmul]
  have incoming : Group.OnCurve (RuntimeBalanceVariableWindow000Point0Cones.coefficientD : F)
      (RuntimeBalanceVariableWindow000Point1Completion.inputPoint rho) := by
    rw [addition_input]; exact first.2
  have rightCurve : Group.OnCurve (RuntimeBalanceVariableWindow000Point0Cones.coefficientD : F)
      (RuntimeBalanceVariableWindow000Point1Completion.rightPoint rho) := by
    rw [addition_base]; exact baseCurve
  have second := RuntimeBalanceVariableWindow000Point1Soundness.actual_point_sound rho one four imaginary
    nonSquare imaginarySquare incoming rightCurve secondRows
  have tripleMeaning : RuntimeBalanceVariableWindow000Point1Completion.outputPoint rho = model.coordinates (3 • base) := by
    rw [second,addition_input,twiceMeaning,addition_base,baseMeaning]
    change Group.affineAdd (RuntimeBalanceVariableWindow000Point0Cones.coefficientD : F)
      (model.coordinates (2 • base)) (model.coordinates base) = model.coordinates (3 • base)
    rw [← model.addition]
    congr 1
    simp only [show (3 : Nat) = 2 + 1 from rfl,add_nsmul,one_nsmul]
  constructor
  · exact baseMeaning
  · constructor
    · simpa only [RuntimeBalanceVariableWindow000Program.tables,GroupFixedCircuitCompletion.point,
        RuntimeBalanceVariableWindow000Point0Completion.outputPoint,GroupQuotientPairCompletion.point,
        RuntimeBalanceVariableWindow000Point0Completion.x,RuntimeBalanceVariableWindow000Point0Completion.y,
        eval,Int.cast_one,one_mul,add_zero] using twiceMeaning
    · simpa only [RuntimeBalanceVariableWindow000Program.tables,GroupFixedCircuitCompletion.point,
        RuntimeBalanceVariableWindow000Point1Completion.outputPoint,GroupQuotientPairCompletion.point,
        RuntimeBalanceVariableWindow000Point1Completion.x,RuntimeBalanceVariableWindow000Point1Completion.y,
        eval,Int.cast_one,one_mul,add_zero] using tripleMeaning

set_option pp.all true in
#check @addition_input
#print axioms addition_input
set_option pp.all true in
#check @addition_base
#print axioms addition_base
set_option pp.all true in
#check @native_tables
#print axioms native_tables
end ShielddSecurity.RuntimeBalanceVariableTableSoundness
