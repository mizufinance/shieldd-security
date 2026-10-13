import ShielddSecurity.AuthorizationSharedFrame418
import ShielddSecurity.AuthorizationRingProduct420A
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationSharedFrame420B
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def assignment (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  SharedAuthorizationNonidentity413.assignment (AuthorizationSharedSeed416.seed original c w) c w
    authInitial initial senderInitial receiverInitial

def originalBase (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (senderInitial receiverInitial : Fin 3 → Group.Point F) : Nat → F :=
  UserLifecycleWord345.originalBase
    (EncodedWordBits375.base (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed original c w) w authInitial) w senderInitial receiverInitial) w

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original c w authInitial initial senderInitial receiverInitial)
      CapturedFullArithmetic52.rowAt 177954 := by
  exact SharedHighZeroRows333.arithmetic
    (UserWordSeed342.seed (EncodedWordBits375.base
      (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed original c w) w authInitial) w senderInitial receiverInitial) w) c w initial

end ShielddSecurity.AuthorizationSharedFrame420B

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedFrame420B.assignment
#print axioms ShielddSecurity.AuthorizationSharedFrame420B.assignment

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedFrame420B.originalBase
#print axioms ShielddSecurity.AuthorizationSharedFrame420B.originalBase

set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedFrame420B.arithmetic
#print axioms ShielddSecurity.AuthorizationSharedFrame420B.arithmetic
