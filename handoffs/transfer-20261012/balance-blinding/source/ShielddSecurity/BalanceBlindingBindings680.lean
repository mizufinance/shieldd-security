import ShielddSecurity.BalanceBlindingFrame679
import ShielddSecurity.BalanceBlindingLocal676
import ShielddSecurity.BalanceBlindingFrame639
import ShielddSecurity.BalanceSignRow655
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingBindings680
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
attribute [local irreducible] model

noncomputable def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  BalanceSignBindings652.assignment (BalanceBlindingTrace675.seed original w.blinding)
    (BalanceBlindingDomain670.withBlinding c) w legal rkInitial authInitial initial senderInitial receiverInitial
attribute [local irreducible] assignment

theorem preserved (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (inside : BalanceBlindingLayout677.Inside column) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=BalanceBlindingTrace675.seed original w.blinding column := by
  unfold assignment
  exact BalanceBlindingFrame679.sign_frame _ (BalanceBlindingDomain670.withBlinding c) w legal
    rkInitial authInitial initial senderInitial receiverInitial column inside

theorem point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (before : index<126) :
    VariableWindowColumns449.columnPoint (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (22484+2*index)=
      (BalanceBlindingTrace675.window w.blinding index).output := by
  have lower : BalanceBlindingLayout677.Inside (22484+2*index) := by
    refine ⟨22484,by simp [BalanceBlindingLayout677.starts],?_,?_⟩ <;> omega
  have upper : BalanceBlindingLayout677.Inside (22484+2*index+1) := by
    refine ⟨22484,by simp [BalanceBlindingLayout677.starts],?_,?_⟩ <;> omega
  have x := preserved original c w legal rkInitial authInitial initial senderInitial receiverInitial (22484+2*index) lower
  have y := preserved original c w legal rkInitial authInitial initial senderInitial receiverInitial (22484+2*index+1) upper
  have together : VariableWindowColumns449.columnPoint (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (22484+2*index)=
      VariableWindowColumns449.columnPoint (BalanceBlindingTrace675.seed original w.blinding) (22484+2*index) :=
    congrArg₂ Group.Point.mk x y
  exact together.trans (BalanceBlindingTrace675.point original w.blinding index before)

theorem bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (before : index<252) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial (22232+index)=
      if (encodeBits 252 w.blinding)[index]?.getD false then 1 else 0 := by
  unfold assignment BalanceSignBindings652.assignment
  exact BalanceBlindingFrame639.tier_bits _ (BalanceBlindingDomain670.withBlinding c) w legal
    rkInitial authInitial initial senderInitial receiverInitial index before

theorem copied (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial copy=1 := by
  unfold assignment BalanceSignBindings652.assignment
  exact TierFlagBindings630.copied _ (BalanceBlindingDomain670.withBlinding c) w legal rkInitial authInitial initial senderInitial receiverInitial

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
  unfold assignment BalanceSignBindings652.assignment
  exact TierFlagBindings630.arithmetic _ (BalanceBlindingDomain670.withBlinding c) w legal rkInitial authInitial initial senderInitial receiverInitial

theorem sign_row (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) (fun i => CapturedFullRelation58.rowAt (199867+i)) 1 := by
  unfold assignment
  exact BalanceSignRow655.row _ (BalanceBlindingDomain670.withBlinding c) w legal rkInitial authInitial initial senderInitial receiverInitial

theorem scalar_bound (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w) : w.blinding<2^252 := by
  have bound := BalanceBlindingBits638.scalar_bound
    (ConcreteAuthorizationCrypto430.withOperations
      (AuthorizationFixedDomain485.withGenerator (DetectionGroupDomain611.baseCrypto (BalanceBlindingDomain670.withBlinding c)))) w legal
  exact lt_of_lt_of_le bound (by decide : TransferCore.scalarOrder≤2^252)

theorem final_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VariableWindowColumns449.columnPoint (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) 22734=
      SubgroupSeedCompletion203.fieldPoint ((BalanceBlindingDomain670.crypto c).mul w.blinding
        (BalanceBlindingDomain670.crypto c).blindingGenerator) := by
  have result := point original c w legal rkInitial authInitial initial senderInitial receiverInitial 125 (by decide)
  change VariableWindowColumns449.columnPoint (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) 22734=
    (BalanceBlindingTrace675.window w.blinding 125).output at result
  have bound := scalar_bound c w legal
  exact (result.trans (BalanceBlindingLocal676.last_output w.blinding bound)).trans
    (BalanceBlindingDomain670.multiply_coordinates c w.blinding
      (lt_of_lt_of_le bound (by decide : 2^252≤2^255))).symm
end ShielddSecurity.BalanceBlindingBindings680

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBindings680.preserved
#print axioms ShielddSecurity.BalanceBlindingBindings680.preserved

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBindings680.point
#print axioms ShielddSecurity.BalanceBlindingBindings680.point

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBindings680.bits
#print axioms ShielddSecurity.BalanceBlindingBindings680.bits

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBindings680.copied
#print axioms ShielddSecurity.BalanceBlindingBindings680.copied

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBindings680.arithmetic
#print axioms ShielddSecurity.BalanceBlindingBindings680.arithmetic

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBindings680.sign_row
#print axioms ShielddSecurity.BalanceBlindingBindings680.sign_row

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBindings680.scalar_bound
#print axioms ShielddSecurity.BalanceBlindingBindings680.scalar_bound

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingBindings680.final_point
#print axioms ShielddSecurity.BalanceBlindingBindings680.final_point
