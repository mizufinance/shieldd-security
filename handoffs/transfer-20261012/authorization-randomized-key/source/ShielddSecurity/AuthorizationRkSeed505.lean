import ShielddSecurity.AuthorizationRkDomain503
import ShielddSecurity.AuthorizationRkFrame502
import ShielddSecurity.AuthorizationAddDomain504
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationRkSeed505
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def value (w : TransferSem.Witness) (initial : Group.Point F) (offset : Nat) : F :=
  if offset=0 then (w.auth.rk.x:F)
  else if offset=1 then (w.auth.rk.y:F)
  else if offset=2 then initial.x
  else if offset=3 then initial.y
  else if offset<7 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) initial (offset-4)
  else (w.auth.rk.x:F)⁻¹

def seed (original : Nat → F) (w : TransferSem.Witness) (rkInitial : Group.Point F) (column : Nat) : F :=
  if column=4271 then (AuthorizationAddDomain504.denominator w)⁻¹
  else if 4272≤column ∧ column<4280 then value w rkInitial (column-4272)
  else original column

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  AuthorizationFixedSeed487.assignment (seed original w rkInitial) c w legal authInitial initial senderInitial receiverInitial

theorem completed_hint (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) (inside : 4271≤column ∧ column≤4279) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial column=seed original w rkInitial column := by
  let chosen := AuthorizationFixedDomain485.withGenerator c
  let fixed := AuthorizationFixedSeed487.seed (seed original w rkInitial) w.auth.randomizer
  let dh := AuthorizationDhSeed473.seed fixed chosen w legal
  let traced := AuthorizationTraceSeed451.seed dh (AuthorizationTraceAssignment457.bases chosen w legal) w.auth.ivk
  have preserved := AuthorizationRkFrame502.completed_hint (IvkInverseSeed426.seed traced w)
    (ConcreteAuthorizationCrypto430.withOperations chosen) w authInitial initial senderInitial receiverInitial column inside
  apply preserved.trans
  rw [IvkInverseSeed426.outside traced w column (by omega)]
  dsimp only [traced]
  rw [AuthorizationTraceSeed451.outside dh (AuthorizationTraceAssignment457.bases chosen w legal) w.auth.ivk column (Or.inr (by omega))]
  have outside : dh column=fixed column := by
    simp only [dh,AuthorizationDhSeed473.seed,if_neg (show column≠3765 by omega)]
  exact outside.trans (AuthorizationFixedSeed487.outside (seed original w rkInitial) w.auth.randomizer column (Or.inr (by omega)))

theorem completed_value (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (offset : Fin 8) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial (4272+offset.val)=value w rkInitial offset.val := by
  rw [completed_hint original c w legal rkInitial authInitial initial senderInitial receiverInitial _ (by have := offset.isLt;omega)]
  have inside : 4272≤4272+offset.val ∧ 4272+offset.val<4280 := by have := offset.isLt;omega
  simp only [seed,if_neg (show ¬4272+offset.val=4271 by omega),if_pos inside,Nat.add_sub_cancel_left]

theorem completed_inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 4271=(AuthorizationAddDomain504.denominator w)⁻¹ := by
  rw [completed_hint original c w legal rkInitial authInitial initial senderInitial receiverInitial _ (by constructor <;> decide)]
  simp only [seed,if_pos rfl,if_true]

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 :=
  AuthorizationFixedBindings492.arithmetic (seed original w rkInitial) c w legal authInitial initial senderInitial receiverInitial

theorem copied (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial copy=1 :=
  AuthorizationFixedBindings492.copied (seed original w rkInitial) c w legal authInitial initial senderInitial receiverInitial

theorem zero (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 :=
  AuthorizationDhSeed473.zero (AuthorizationFixedSeed487.seed (seed original w rkInitial) w.auth.randomizer)
    (AuthorizationFixedDomain485.withGenerator c) w legal authInitial initial senderInitial receiverInitial
end ShielddSecurity.AuthorizationRkSeed505

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkSeed505.value
#print axioms ShielddSecurity.AuthorizationRkSeed505.value

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkSeed505.seed
#print axioms ShielddSecurity.AuthorizationRkSeed505.seed

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkSeed505.assignment
#print axioms ShielddSecurity.AuthorizationRkSeed505.assignment

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkSeed505.completed_hint
#print axioms ShielddSecurity.AuthorizationRkSeed505.completed_hint

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkSeed505.completed_value
#print axioms ShielddSecurity.AuthorizationRkSeed505.completed_value

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkSeed505.completed_inverse
#print axioms ShielddSecurity.AuthorizationRkSeed505.completed_inverse

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkSeed505.arithmetic
#print axioms ShielddSecurity.AuthorizationRkSeed505.arithmetic

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkSeed505.copied
#print axioms ShielddSecurity.AuthorizationRkSeed505.copied

set_option pp.all true in
#check @ShielddSecurity.AuthorizationRkSeed505.zero
#print axioms ShielddSecurity.AuthorizationRkSeed505.zero
