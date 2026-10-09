import ShielddSecurity.RuntimeBalanceVariableWindow001Program
import ShielddSecurity.RuntimeBalanceVariableWindow001WindowSoundness
import ShielddSecurity.RuntimeBalanceVariableWindow000Program
import ShielddSecurity.RuntimeBalanceVariableWindow000FoldedSoundness
import ShielddSecurity.GroupVariableCircuitSoundness

set_option maxHeartbeats 250000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeBalanceVariableProgramSoundness

theorem later {F : Type} [Field F] [CharP F RuntimeBalanceVariableWindow001CurveCompletion.modulus]
    (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeBalanceVariableWindow001CurveCompletion.d : F))
    (imaginarySquare : imaginary * imaginary = -1) (lowBit highBit : Bool) :
    GroupVariableCircuitSoundness.LocalSound (RuntimeBalanceVariableWindow001CurveCompletion.d : F)
      200692 RuntimeBalanceVariableWindow001Program.tables
      (RuntimeBalanceVariableWindow001Program.program lowBit highBit) := by
  intro rho one linked incoming curved low high satisfied
  change Satisfies rho RuntimeBalanceVariableWindow001WindowSoundness.rawRows at satisfied
  have result := RuntimeBalanceVariableWindow001WindowSoundness.actual_window_sound rho one four
    imaginary nonSquare imaginarySquare lowBit highBit incoming low high curved.1 curved.2.1 curved.2.2 satisfied
  simpa only [RuntimeBalanceVariableWindow001Program.program,RuntimeBalanceVariableWindow001Program.tables,
    GroupFixedCircuitCompletion.point,RuntimeBalanceVariableWindow001Point7Completion.outputPoint,
    GroupQuotientPairCompletion.point,RuntimeBalanceVariableWindow001Point7Completion.x,
    RuntimeBalanceVariableWindow001Point7Completion.y,RuntimeBalanceVariableWindow001Point5Completion.inputPoint,
    RuntimeBalanceVariableWindow001Point5Completion.inputX,RuntimeBalanceVariableWindow001Point5Completion.inputY,
    RuntimeBalanceVariableWindow001Point7SelectorSoundness.basePoint,
    RuntimeBalanceVariableWindow001Point7SelectorSoundness.twicePoint,
    RuntimeBalanceVariableWindow001Point7SelectorSoundness.triplePoint,
    RuntimeBalanceVariableWindow001Point7SelectorSoundness.baseX,
    RuntimeBalanceVariableWindow001Point7SelectorSoundness.baseY,
    RuntimeBalanceVariableWindow001Point7SelectorSoundness.twiceX,
    RuntimeBalanceVariableWindow001Point7SelectorSoundness.twiceY,
    RuntimeBalanceVariableWindow001Point7SelectorSoundness.tripleX,
    RuntimeBalanceVariableWindow001Point7SelectorSoundness.tripleY,
    RuntimeBalanceVariableWindow001Point7SelectorSoundness.low,
    RuntimeBalanceVariableWindow001Point7SelectorSoundness.high,
    RuntimeBalanceVariableWindow001Point7SelectorCompletion.low,
    RuntimeBalanceVariableWindow001Point7SelectorCompletion.high,
    eval,Int.cast_one,one_mul,add_zero] using result

theorem first {F : Type} [Field F] [CharP F RuntimeBalanceVariableWindow000FoldedCompletion.modulus]
    (lowBit highBit : Bool) :
    GroupVariableCircuitSoundness.LocalSound (RuntimeBalanceVariableWindow000Point4Cones.coefficientD : F)
      200692 RuntimeBalanceVariableWindow000Program.tables
      (RuntimeBalanceVariableWindow000Program.program lowBit highBit) := by
  intro rho one linked incoming curved low high satisfied
  change Satisfies rho RuntimeBalanceVariableWindow000FoldedSoundness.rawRows at satisfied
  have result := RuntimeBalanceVariableWindow000FoldedSoundness.actual_window_sound rho one satisfied
  have identity : GroupFixedCircuitCompletion.point rho
      (RuntimeBalanceVariableWindow000Program.program lowBit highBit).input = Group.identityPoint := by
    simp only [RuntimeBalanceVariableWindow000Program.program,GroupFixedCircuitCompletion.point,
      Group.identityPoint,eval,Int.cast_one,one_mul,add_zero,one]
  rw [identity,GroupVariableCircuitNative.affine_identity_left,
    GroupVariableCircuitNative.affine_identity_left,GroupVariableCircuitNative.affine_identity_left]
  simpa only [RuntimeBalanceVariableWindow000Program.program,RuntimeBalanceVariableWindow000Program.tables,
    GroupFixedCircuitCompletion.point,RuntimeBalanceVariableWindow000FoldedSoundness.output,
    RuntimeBalanceVariableWindow000Point4SelectorSoundness.basePoint,
    RuntimeBalanceVariableWindow000Point4SelectorSoundness.twicePoint,
    RuntimeBalanceVariableWindow000Point4SelectorSoundness.triplePoint,
    RuntimeBalanceVariableWindow000Point4SelectorSoundness.baseX,
    RuntimeBalanceVariableWindow000Point4SelectorSoundness.baseY,
    RuntimeBalanceVariableWindow000Point4SelectorSoundness.twiceX,
    RuntimeBalanceVariableWindow000Point4SelectorSoundness.twiceY,
    RuntimeBalanceVariableWindow000Point4SelectorSoundness.tripleX,
    RuntimeBalanceVariableWindow000Point4SelectorSoundness.tripleY,
    RuntimeBalanceVariableWindow000Point4SelectorSoundness.low,
    RuntimeBalanceVariableWindow000Point4SelectorSoundness.high,
    RuntimeBalanceVariableWindow000FoldedCurveCompletion.low,
    RuntimeBalanceVariableWindow000FoldedCurveCompletion.high,
    eval,Int.cast_one,one_mul,add_zero] using result

set_option pp.all true in
#check @later
#print axioms later
set_option pp.all true in
#check @first
#print axioms first
end ShielddSecurity.RuntimeBalanceVariableProgramSoundness
