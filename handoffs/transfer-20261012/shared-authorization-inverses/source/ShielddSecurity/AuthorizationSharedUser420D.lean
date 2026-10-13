import ShielddSecurity.AuthorizationSharedCopy420C
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationSharedUser420D
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem AuthorizationSharedFrame420B

theorem user_value (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (slot : Fin 3) :
    assignment original c w authInitial initial senderInitial receiverInitial (1504+8*slot.val)=
      ((UserPointDomain351.point w.sender slot).x:F) := by
  have value := UserSubgroupFrame354.sender_value
    (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed
      (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed original c w) w authInitial) w) w) w)
    c w initial senderInitial receiverInitial slot ⟨0,by decide⟩
  simpa only [Nat.add_zero] using value

end ShielddSecurity.AuthorizationSharedUser420D
set_option pp.all true in
#check @ShielddSecurity.AuthorizationSharedUser420D.user_value
#print axioms ShielddSecurity.AuthorizationSharedUser420D.user_value
