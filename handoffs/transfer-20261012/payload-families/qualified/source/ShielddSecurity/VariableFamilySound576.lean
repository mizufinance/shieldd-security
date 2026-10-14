import ShielddSecurity.VariableFamilyColumns563
import ShielddSecurity.ConcreteRegistrySharedEncoding294
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableFamilySound576
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open VariableFamilyLayout562
open VariableFamilyColumns563 (columnPoint)
attribute [local irreducible] model

theorem output (rho : Nat → F) (base acc : curve.Point) (low high : Bool)
    (family : Family) (window : Nat) (entry : VariableWindowJoin443.Entry)
    (checked : checkComplete ⟨family,window,entry⟩=true)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (baseMeaning : VariableWindowJoin443.point rho family.baseX family.baseY=model.coordinates base)
    (twice : columnPoint rho family.precomputeX=model.coordinates (2 • base))
    (triple : columnPoint rho (family.precomputeX+2)=model.coordinates (3 • base))
    (previousMeaning : columnPoint rho (previous family window)=model.coordinates acc)
    (lowBit : rho (family.bitsStart+250-2*window)=if low then 1 else 0)
    (highBit : rho (family.bitsStart+251-2*window)=if high then 1 else 0)
    (satisfied : VariableWindowJoin443.Rows rho entry) :
    columnPoint rho (previous family window+6)=
      model.coordinates (4 • acc+(low.toNat+2*high.toNat) • base) := by
  have complete : Complete ⟨family,window,entry⟩ := of_decide_eq_true checked
  rcases complete with ⟨layout,wiring,first,second,addition,selector⟩
  have equations := (VariableFamilyColumns563.equations_iff family window entry layout wiring first second addition selector
    rho one arithmetic low high lowBit highBit).mp satisfied
  rw [baseMeaning,twice,triple,previousMeaning] at equations
  exact TransferOwnership.window_coordinates (CapturedFirstSubgroup81.d:F) imaginary model
    (by rw [coefficient_eq];exact ConcreteJubjubField01.coefficient_no_unit_square)
    imaginary_square acc base low high _ _ _ equations.1 equations.2.1 equations.2.2
end ShielddSecurity.VariableFamilySound576
set_option pp.all true in
#check @ShielddSecurity.VariableFamilySound576.output
#print axioms ShielddSecurity.VariableFamilySound576.output
