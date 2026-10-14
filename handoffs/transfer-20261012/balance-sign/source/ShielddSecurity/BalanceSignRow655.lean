import ShielddSecurity.BalanceWordValues653
import ShielddSecurity.BalanceSignCapture654
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceSignRow655
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open BalanceSignBindings652 (assignment negative)
attribute [local irreducible] assignment

theorem row (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (DetectionGroupDomain611.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CompilerAssertionBlock51.SatisfiesAt
      (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (199867+i)) 1 := by
  let rho := assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 := by
    dsimp only [rho]
    unfold assignment
    exact TierFlagBindings630.arithmetic (BalanceSignBindings652.seed original w) c w legal
      rkInitial authInitial initial senderInitial receiverInitial
  apply (BalanceSignCapture654.rows_iff rho arithmetic).mpr
  have input0 := BalanceWordValues653.values original c w legal rkInitial authInitial initial
    senderInitial receiverInitial 4281 (by decide +kernel)
  change rho 4281=((w.spends 0).amount:F) at input0
  have input1 := BalanceWordValues653.values original c w legal rkInitial authInitial initial
    senderInitial receiverInitial 4534 (by decide +kernel)
  change rho 4534=((w.spends 1).amount:F) at input1
  have output0 := BalanceWordValues653.values original c w legal rkInitial authInitial initial
    senderInitial receiverInitial 4789 (by decide +kernel)
  change rho 4789=((w.outputs 0).amount:F) at output0
  have output1 := BalanceWordValues653.values original c w legal rkInitial authInitial initial
    senderInitial receiverInitial 6194 (by decide +kernel)
  change rho 6194=((w.outputs 1).amount:F) at output1
  have magnitude := BalanceWordValues653.values original c w legal rkInitial authInitial initial
    senderInitial receiverInitial 21712 (by decide +kernel)
  change rho 21712=(RemainingWordSeed369.magnitude w:F) at magnitude
  have flag := BalanceSignBindings652.flag original c w legal rkInitial authInitial initial senderInitial receiverInitial
  change rho 21711=(if negative w then 1 else 0) at flag
  rw [input0,input1,output0,output1,magnitude,flag]
  have signed := BalanceSignBindings652.signed_magnitude w
  push_cast at signed
  cases value : negative w <;>
    simp only [value,Bool.false_eq_true,if_false,if_true] at signed ⊢ <;>
    linear_combination -signed
end ShielddSecurity.BalanceSignRow655
set_option pp.all true in
#check @ShielddSecurity.BalanceSignRow655.row
#print axioms ShielddSecurity.BalanceSignRow655.row
