import ShielddSecurity.AuthorizationTraceSeed451
import ShielddSecurity.IvkInverseConstruction429
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationTraceAssignment457
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open ConcreteAuthorizationCrypto430 (withOperations)

def bases (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) (index : Nat) : curve.Point :=
  if index=0 then AuthorizationGroupDomain445.represented c w legal ⟨0,by decide⟩
  else AuthorizationGroupDomain445.represented c w legal ⟨2,by decide⟩

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  IvkInverseSeed426.assignment (AuthorizationTraceSeed451.seed original (bases c w legal) w.auth.ivk)
    (withOperations c) w authInitial initial senderInitial receiverInitial

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal authInitial initial senderInitial receiverInitial)
      CapturedFullArithmetic52.rowAt 177954 :=
  AuthorizationSharedFrame420B.arithmetic (IvkInverseSeed426.seed (AuthorizationTraceSeed451.seed original (bases c w legal) w.auth.ivk) w) (withOperations c) w authInitial initial senderInitial receiverInitial

theorem copied (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal authInitial initial senderInitial receiverInitial copy=1 :=
  AuthorizationSharedCopy420C.copied (IvkInverseSeed426.seed (AuthorizationTraceSeed451.seed original (bases c w legal) w.auth.ivk) w) (withOperations c) w authInitial initial senderInitial receiverInitial

theorem hints (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat)
    (lower : 2253≤column) (upper : column≤3764) :
    assignment original c w legal authInitial initial senderInitial receiverInitial column=
      AuthorizationTraceSeed451.seed original (bases c w legal) w.auth.ivk column :=
  AuthorizationTraceSeed451.completed_hint (AuthorizationTraceSeed451.seed original (bases c w legal) w.auth.ivk) (withOperations c) w authInitial initial senderInitial receiverInitial column lower upper

theorem retained (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      IvkInverseConstruction429.Earlier (AuthorizationTraceSeed451.seed original (bases c w legal) w.auth.ivk)
        (withOperations c) w authInitial senderInitial receiverInitial initial ∧
      CapturedIvkInverse427.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) :=
  IvkInverseConstruction429.legal_completed (AuthorizationTraceSeed451.seed original (bases c w legal) w.auth.ivk) (withOperations c) w legal
end ShielddSecurity.AuthorizationTraceAssignment457

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceAssignment457.bases
#print axioms ShielddSecurity.AuthorizationTraceAssignment457.bases

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceAssignment457.assignment
#print axioms ShielddSecurity.AuthorizationTraceAssignment457.assignment

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceAssignment457.arithmetic
#print axioms ShielddSecurity.AuthorizationTraceAssignment457.arithmetic

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceAssignment457.copied
#print axioms ShielddSecurity.AuthorizationTraceAssignment457.copied

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceAssignment457.hints
#print axioms ShielddSecurity.AuthorizationTraceAssignment457.hints

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceAssignment457.retained
#print axioms ShielddSecurity.AuthorizationTraceAssignment457.retained
