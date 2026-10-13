import ShielddSecurity.IvkInverseDomain425
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.IvkInverseSeed426
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column=2252 then (w.auth.ivk:F)⁻¹ else original column

theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat) (out : column≠2252) :
    seed original w column=original column := by simp only [seed,if_neg out]

theorem value (original : Nat → F) (w : TransferSem.Witness) :
    seed original w 2252=(w.auth.ivk:F)⁻¹ := by unfold seed; rw [if_pos rfl]

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  AuthorizationSharedFrame420B.assignment (seed original w) c w authInitial initial senderInitial receiverInitial

theorem completed_inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w authInitial initial senderInitial receiverInitial 2252=(w.auth.ivk:F)⁻¹ :=
  (AuthorizationMultiplyFrame424.completed_hint (seed original w) c w authInitial initial senderInitial receiverInitial
    2252 (by constructor <;> decide)).trans (value original w)
end ShielddSecurity.IvkInverseSeed426

set_option pp.all true in
#check @ShielddSecurity.IvkInverseSeed426.seed
#print axioms ShielddSecurity.IvkInverseSeed426.seed

set_option pp.all true in
#check @ShielddSecurity.IvkInverseSeed426.outside
#print axioms ShielddSecurity.IvkInverseSeed426.outside

set_option pp.all true in
#check @ShielddSecurity.IvkInverseSeed426.value
#print axioms ShielddSecurity.IvkInverseSeed426.value

set_option pp.all true in
#check @ShielddSecurity.IvkInverseSeed426.assignment
#print axioms ShielddSecurity.IvkInverseSeed426.assignment

set_option pp.all true in
#check @ShielddSecurity.IvkInverseSeed426.completed_inverse
#print axioms ShielddSecurity.IvkInverseSeed426.completed_inverse
