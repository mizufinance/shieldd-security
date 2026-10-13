import ShielddSecurity.AuthorizationSharedFrame420B
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationSharedCopy420C
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem AuthorizationSharedFrame420B

theorem copied (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w authInitial initial senderInitial receiverInitial copy=1 := by
  have zero := SharedHighZeroRows333.zero
    (UserWordSeed342.seed (EncodedWordBits375.base
      (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed original c w) w authInitial) w senderInitial receiverInitial) w) c w initial
  have linked := SharedComparisonBlocks327.linked
    (HighZeroSeed329.seed (UserWordSeed342.seed (EncodedWordBits375.base
      (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed original c w) w authInitial) w senderInitial receiverInitial) w) w) c w initial
  exact linked.trans zero


end ShielddSecurity.AuthorizationSharedCopy420C
set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedCopy420C.copied
#print axioms ShielddSecurity.AuthorizationSharedCopy420C.copied
