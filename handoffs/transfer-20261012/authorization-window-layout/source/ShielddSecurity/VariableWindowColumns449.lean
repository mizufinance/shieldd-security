import ShielddSecurity.VariableWindowLayout447
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableWindowColumns449
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 VariableWindowLayout447

def columnPoint {F : Type} [Field F] (rho : Nat → F) (column : Nat) : Group.Point F :=
  ⟨rho column,rho (column+1)⟩
def witness {F : Type} [Field F] (rho : Nat → F) (family : Family) (window : Nat)
    (low high : Bool) : TransferOwnership.WindowWitness F :=
  ⟨low,high,columnPoint rho (previous family window+2),columnPoint rho (previous family window+4),
    columnPoint rho (previous family window+6)⟩
variable {F : Type} [Field F] [CharP F p]
theorem equations_iff (family : Family) (window : Nat) (e : VariableWindowJoin443.Entry)
    (layout : check family window e=true) (wiring : VariableWindowJoin443.check e=true)
    (first : VariableOperationAdapter434.check e.first=true)
    (second : VariableOperationAdapter434.check e.second=true)
    (addition : VariableOperationAdapter434.check e.addition=true)
    (selector : VariableSelectorAdapter437.check e.selector=true) (rho : Nat → F)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (low high : Bool) (lowBit : rho (2250-2*window)=(if low then 1 else 0))
    (highBit : rho (2251-2*window)=(if high then 1 else 0)) :
    VariableWindowJoin443.Rows rho e ↔
    TransferOwnership.WindowEquations (CapturedFirstSubgroup81.d:F)
      (columnPoint rho family.baseX) (columnPoint rho family.precomputeX)
      (columnPoint rho (family.precomputeX+2)) (columnPoint rho (previous family window))
      (witness rho family window low high) := by
  have v0 := value family window e layout rho (VariableOperationAdapter434.port e.first 1) (previous family window) (by exact List.mem_cons.mpr (Or.inl rfl))
  have v1 := value family window e layout rho (VariableOperationAdapter434.port e.first 2) (previous family window+1) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  have v2 := value family window e layout rho (VariableOperationAdapter434.port e.first 3) (previous family window+2) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))
  have v3 := value family window e layout rho (VariableOperationAdapter434.port e.first 4) (previous family window+3) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))
  have v4 := value family window e layout rho (VariableOperationAdapter434.port e.second 3) (previous family window+4) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))
  have v5 := value family window e layout rho (VariableOperationAdapter434.port e.second 4) (previous family window+5) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))
  have v6 := value family window e layout rho (VariableOperationAdapter434.port e.addition 5) (previous family window+6) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))
  have v7 := value family window e layout rho (VariableOperationAdapter434.port e.addition 6) (previous family window+7) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))
  have v8 := value family window e layout rho (VariableSelectorAdapter437.port e.selector 1) (2250-2*window) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))
  have v9 := value family window e layout rho (VariableSelectorAdapter437.port e.selector 2) (2251-2*window) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))
  have v10 := value family window e layout rho (VariableSelectorAdapter437.port e.selector 3) (family.baseX) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))
  have v11 := value family window e layout rho (VariableSelectorAdapter437.port e.selector 4) (family.baseX+1) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))
  have v12 := value family window e layout rho (VariableSelectorAdapter437.port e.selector 5) (family.precomputeX) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))
  have v13 := value family window e layout rho (VariableSelectorAdapter437.port e.selector 6) (family.precomputeX+1) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))
  have v14 := value family window e layout rho (VariableSelectorAdapter437.port e.selector 7) (family.precomputeX+2) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))
  have v15 := value family window e layout rho (VariableSelectorAdapter437.port e.selector 8) (family.precomputeX+3) (by exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))))))))))))))))))))))))
  have result := VariableWindowJoin443.equations_iff e wiring first second addition selector rho one arithmetic
    low high (v8.trans lowBit) (v9.trans highBit)
  simpa only [VariableWindowJoin443.selectorPoint,VariableWindowJoin443.opPoint,
    VariableWindowJoin443.point,VariableWindowJoin443.witness,witness,columnPoint,
    v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,v12,v13,v14,v15] using result
end ShielddSecurity.VariableWindowColumns449

set_option pp.all true in
#check @ShielddSecurity.VariableWindowColumns449.columnPoint
#print axioms ShielddSecurity.VariableWindowColumns449.columnPoint

set_option pp.all true in
#check @ShielddSecurity.VariableWindowColumns449.witness
#print axioms ShielddSecurity.VariableWindowColumns449.witness

set_option pp.all true in
#check @ShielddSecurity.VariableWindowColumns449.equations_iff
#print axioms ShielddSecurity.VariableWindowColumns449.equations_iff
