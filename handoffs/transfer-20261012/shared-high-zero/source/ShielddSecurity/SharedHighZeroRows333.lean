import ShielddSecurity.HighZeroCompletionFrame332
import ShielddSecurity.WeightedDelta335
import ShielddSecurity.SharedZeroConstant336
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedHighZeroRows333
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open HighZeroCompletionFrame332

theorem first_delta (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    eval (assignment original c w initial) CapturedHighZero126.delta=HighZeroSeed329.firstDelta w := by
  have a := SharedComparisonBlocks327.asset_high (HighZeroSeed329.seed original w) c w initial legal
  have b := SharedComparisonBlocks327.value_high (HighZeroSeed329.seed original w) c w initial legal
  exact WeightedDelta335.meaning (assignment original c w initial)
    CapturedRegistryHighLimb120.leftColumns CapturedRegistryHighLimb120.rightColumns _ _ a b


set_option pp.all true in
#check @ShielddSecurity.SharedHighZeroRows333.first_delta
#print axioms ShielddSecurity.SharedHighZeroRows333.first_delta

theorem second_delta (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    eval (assignment original c w initial) CapturedNextHighZero138.delta=HighZeroSeed329.secondDelta w := by
  have a := SharedComparisonBlocks327.next_high (HighZeroSeed329.seed original w) c w initial legal
  have b := SharedComparisonBlocks327.asset_high (HighZeroSeed329.seed original w) c w initial legal
  exact WeightedDelta335.meaning (assignment original c w initial)
    CapturedNextHighLimb133.leftColumns CapturedNextHighLimb133.rightColumns _ _ a b


set_option pp.all true in
#check @ShielddSecurity.SharedHighZeroRows333.second_delta
#print axioms ShielddSecurity.SharedHighZeroRows333.second_delta

theorem zero (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) :
    assignment original c w initial 0=1 := by
  unfold HighZeroCompletionFrame332.assignment SharedComparisonBlocks327.assignment HeaderRegisteredConstruction310.completed
  exact SharedZeroConstant336.subgroup
    (RegisteredConstructorFrame309.prepared (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w) initial
    (LegalWordNormalization272.normalized
      (HeaderRegisteredConstruction310.numbers (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w))
    (HeaderRegisteredConstruction310.fallback (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w)
    (RegisteredConstructorFrame309.prepared_zero (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w)

set_option pp.all true in
#check @ShielddSecurity.SharedHighZeroRows333.zero
#print axioms ShielddSecurity.SharedHighZeroRows333.zero

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness) (initial : Fin 4 → Group.Point F) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial) CapturedFullArithmetic52.rowAt 177954 :=
  by
    unfold HighZeroCompletionFrame332.assignment SharedComparisonBlocks327.assignment HeaderRegisteredConstruction310.completed
    exact SharedWordWitness221.arithmetic
      (CapturedFourSubgroupSeed89.seeded
        (RegisteredConstructorFrame309.prepared (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w) initial)
      (LegalWordNormalization272.normalized
        (HeaderRegisteredConstruction310.numbers (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w))
      (HeaderRegisteredConstruction310.fallback (RegistryComparisonSeed318.seed (HighZeroSeed329.seed original w) w) c w)


set_option pp.all true in
#check @ShielddSecurity.SharedHighZeroRows333.arithmetic
#print axioms ShielddSecurity.SharedHighZeroRows333.arithmetic

theorem first_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial)
      (fun index => CapturedFullRelation58.rowAt (179023+index)) 3 :=
  CapturedHighZero126.complete (assignment original c w initial) (HighZeroSeed329.firstDelta w)
    (arithmetic original c w initial) (first_delta original c w initial legal)
    (HighZeroCompletionFrame332.first_flag original c w initial) (HighZeroCompletionFrame332.first_inverse original c w initial)
    (zero original c w initial) (SharedComparisonBlocks327.linked (HighZeroSeed329.seed original w) c w initial)


set_option pp.all true in
#check @ShielddSecurity.SharedHighZeroRows333.first_rows
#print axioms ShielddSecurity.SharedHighZeroRows333.first_rows

theorem second_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (initial : Fin 4 → Group.Point F) (legal : TransferSem.TransferSem (crypto c) w) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w initial)
      (fun index => CapturedFullRelation58.rowAt (179287+index)) 3 :=
  CapturedNextHighZero138.complete (assignment original c w initial) (HighZeroSeed329.secondDelta w)
    (arithmetic original c w initial) (second_delta original c w initial legal)
    (HighZeroCompletionFrame332.second_flag original c w initial) (HighZeroCompletionFrame332.second_inverse original c w initial)
    (zero original c w initial) (SharedComparisonBlocks327.linked (HighZeroSeed329.seed original w) c w initial)

set_option pp.all true in
#check @ShielddSecurity.SharedHighZeroRows333.second_rows
#print axioms ShielddSecurity.SharedHighZeroRows333.second_rows

end ShielddSecurity.SharedHighZeroRows333
