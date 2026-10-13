import ShielddSecurity.FixedWindowMeaning491
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedWindowCompletion494
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 VariableWindowColumns449

theorem complete (e : FixedWindowJoin488.Entry) (checked : FixedWindowJoin488.check e=true)
    (matched : FixedWindowMeaning491.check e=true) (rho : Nat → F) (one : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (low high : Bool) (previous output : Group.Point F)
    (lowMeaning : rho (3767+2*e.index)=if low then 1 else 0)
    (highMeaning : rho (3768+2*e.index)=if high then 1 else 0)
    (previousMeaning : columnPoint rho (4017+2*e.index)=previous)
    (outputMeaning : columnPoint rho (4019+2*e.index)=output)
    (equations : TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:F) previous
      (Group.windowPoint (if low then 1 else 0) (if high then 1 else 0)
        (FixedSelectorAdapter480.base (AuthorizationFixedTables490.table e.index).1)
        (FixedSelectorAdapter480.twice (AuthorizationFixedTables490.table e.index).1)
        (FixedSelectorAdapter480.triple (AuthorizationFixedTables490.table e.index).1)) output) :
    VariableOperationAdapter434.Rows rho e.operation := by
  apply (FixedWindowJoin488.rows_iff e checked rho one arithmetic).mpr
  have points := FixedWindowMeaning491.points e matched
  rw [lowMeaning,highMeaning,previousMeaning,outputMeaning,points.1,points.2.1,points.2.2]
  exact equations
end ShielddSecurity.FixedWindowCompletion494
set_option pp.all true in
#check @ShielddSecurity.FixedWindowCompletion494.complete
#print axioms ShielddSecurity.FixedWindowCompletion494.complete
