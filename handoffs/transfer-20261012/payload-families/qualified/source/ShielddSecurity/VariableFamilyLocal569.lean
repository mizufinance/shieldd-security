import ShielddSecurity.VariableFamilyColumns563
import ShielddSecurity.AuthorizationTraceLocal453
import ShielddSecurity.VariableTraceBitIndex454
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableFamilyLocal569
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open VariableFamilyLayout562 AuthorizationTraceSeed451
open VariableFamilyColumns563 (columnPoint)
attribute [local irreducible] model

theorem rows (rho : Nat → F) (base : curve.Point) (scalar window : Nat) (family : Family)
    (e : VariableWindowJoin443.Entry) (checked : checkComplete ⟨family,window,e⟩=true)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (baseMeaning : VariableWindowJoin443.point rho family.baseX family.baseY=model.coordinates base)
    (twice : columnPoint rho family.precomputeX=model.coordinates (2 • base))
    (triple : columnPoint rho (family.precomputeX+2)=model.coordinates (3 • base))
    (previousMeaning : columnPoint rho (previous family window)=(windowAt base scalar (window-1)).output)
    (firstMeaning : columnPoint rho (previous family window+2)=(windowAt base scalar window).first)
    (secondMeaning : columnPoint rho (previous family window+4)=(windowAt base scalar window).second)
    (outputMeaning : columnPoint rho (previous family window+6)=(windowAt base scalar window).output)
    (lowBit : rho (family.bitsStart+250-2*window)=if (encodeBits 252 scalar)[250-2*window]?.getD false then 1 else 0)
    (highBit : rho (family.bitsStart+251-2*window)=if (encodeBits 252 scalar)[251-2*window]?.getD false then 1 else 0) :
    VariableWindowJoin443.Rows rho e := by
  have complete : Complete ⟨family,window,e⟩ := of_decide_eq_true checked
  rcases complete with ⟨layout,wiring,first,second,addition,selector⟩
  have valid : Valid family window e := of_decide_eq_true layout
  have pair := VariableTraceBitIndex454.windows_bits model base (encodeBits 252 scalar)
    (by simp) empty window valid.2.1
  change ((windowAt base scalar window).low,(windowAt base scalar window).high)=_ at pair
  have low := congrArg Prod.fst pair
  have high := congrArg Prod.snd pair
  change (windowAt base scalar window).low=(encodeBits 252 scalar)[250-2*window]?.getD false at low
  change (windowAt base scalar window).high=(encodeBits 252 scalar)[251-2*window]?.getD false at high
  apply (VariableFamilyColumns563.equations_iff family window e layout wiring first second addition selector
    rho one arithmetic (windowAt base scalar window).low (windowAt base scalar window).high
    (by rw [low];exact lowBit) (by rw [high];exact highBit)).mpr
  rw [baseMeaning,twice,triple,previousMeaning]
  unfold VariableFamilyColumns563.witness
  rw [firstMeaning,secondMeaning,outputMeaning]
  have equations := AuthorizationTraceLocal453.window_equations base scalar window valid.2.1
  rw [AuthorizationTraceLocal453.before_positive base scalar window valid.1] at equations
  exact equations
end ShielddSecurity.VariableFamilyLocal569
set_option pp.all true in
#check @ShielddSecurity.VariableFamilyLocal569.rows
#print axioms ShielddSecurity.VariableFamilyLocal569.rows
