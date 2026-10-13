import ShielddSecurity.AuthorizationDhColumn476
import ShielddSecurity.AuthorizationTransmission469
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationDhSeed473
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationTraceAssignment457 (bases)
open ConcreteAuthorizationCrypto430 (withOperations)
def seed (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) (column : Nat) : F :=
  if column=3765 then (AuthorizationDhDomain471.point c w legal).x⁻¹ else original column

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  AuthorizationTraceAssignment457.assignment (seed original c w legal) c w legal authInitial initial senderInitial receiverInitial

theorem completed_inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal authInitial initial senderInitial receiverInitial 3765=
      (AuthorizationDhDomain471.point c w legal).x⁻¹ := by
  let before := AuthorizationTraceSeed451.seed (seed original c w legal) (bases c w legal) w.auth.ivk
  have preserved := AuthorizationMultiplyFrame424.completed_hint (IvkInverseSeed426.seed before w)
    (withOperations c) w authInitial initial senderInitial receiverInitial 3765 (by constructor <;> decide)
  have inverseOutside := IvkInverseSeed426.outside before w 3765 (by decide)
  have traceOutside := AuthorizationTraceSeed451.outside (seed original c w legal) (bases c w legal) w.auth.ivk 3765 (Or.inr (by decide))
  exact preserved.trans (inverseOutside.trans (traceOutside.trans (by unfold seed;rw [if_pos rfl])))

theorem completed_x (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal authInitial initial senderInitial receiverInitial 3763=
      (AuthorizationDhDomain471.point c w legal).x :=
  AuthorizationDhColumn476.completed_x (seed original c w legal) c w legal authInitial initial senderInitial receiverInitial

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal authInitial initial senderInitial receiverInitial)
      CapturedFullArithmetic52.rowAt 177954 :=
  AuthorizationTraceAssignment457.arithmetic (seed original c w legal) c w legal authInitial initial senderInitial receiverInitial

theorem copied (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal authInitial initial senderInitial receiverInitial copy=1 :=
  AuthorizationTraceAssignment457.copied (seed original c w legal) c w legal authInitial initial senderInitial receiverInitial

theorem zero (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal authInitial initial senderInitial receiverInitial 0=1 := by
  let before := IvkInverseSeed426.seed (AuthorizationTraceSeed451.seed (seed original c w legal) (bases c w legal) w.auth.ivk) w
  exact SharedHighZeroRows333.zero
    (UserWordSeed342.seed (EncodedWordBits375.base
      (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed before (withOperations c) w) w authInitial)
        w senderInitial receiverInitial) w) (withOperations c) w initial

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  IvkInverseConstruction429.Earlier (AuthorizationTraceSeed451.seed (seed original c w legal) (bases c w legal) w.auth.ivk)
    (withOperations c) w authInitial senderInitial receiverInitial initial ∧
  CapturedIvkInverse427.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
  AuthorizationWindowBlock461.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
  AuthorizationPrefixConstruction464.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
  AuthorizationInitial466.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) ∧
  AuthorizationTransmission469.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial)

theorem retained (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal authInitial initial senderInitial receiverInitial :=
  AuthorizationTransmission469.legal_completed (seed original c w legal) c w legal
end ShielddSecurity.AuthorizationDhSeed473

set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhSeed473.seed
#print axioms ShielddSecurity.AuthorizationDhSeed473.seed

set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhSeed473.assignment
#print axioms ShielddSecurity.AuthorizationDhSeed473.assignment

set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhSeed473.completed_inverse
#print axioms ShielddSecurity.AuthorizationDhSeed473.completed_inverse

set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhSeed473.completed_x
#print axioms ShielddSecurity.AuthorizationDhSeed473.completed_x

set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhSeed473.arithmetic
#print axioms ShielddSecurity.AuthorizationDhSeed473.arithmetic

set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhSeed473.copied
#print axioms ShielddSecurity.AuthorizationDhSeed473.copied

set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhSeed473.zero
#print axioms ShielddSecurity.AuthorizationDhSeed473.zero

set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhSeed473.Earlier
#print axioms ShielddSecurity.AuthorizationDhSeed473.Earlier

set_option pp.all true in
#check @ShielddSecurity.AuthorizationDhSeed473.retained
#print axioms ShielddSecurity.AuthorizationDhSeed473.retained
