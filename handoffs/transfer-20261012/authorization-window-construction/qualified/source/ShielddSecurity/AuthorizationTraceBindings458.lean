import ShielddSecurity.AuthorizationTraceAssignment457
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationTraceBindings458
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open ConcreteAuthorizationCrypto430 (withOperations)
open AuthorizationTraceAssignment457
theorem sender_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (slot : Fin 3) :
    VariableWindowColumns449.columnPoint
      (assignment original c w legal authInitial initial senderInitial receiverInitial) (1504+8*slot.val)=
    SubgroupSeedCompletion203.fieldPoint (UserPointDomain351.point w.sender slot) := by
  have coordinate (offset : Fin 8) := UserSubgroupFrame354.sender_value
    (UserPathSeed361.seed (AuthScalarSeed366.seed (RemainingWordSeed369.seed
      (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed (IvkInverseSeed426.seed (AuthorizationTraceSeed451.seed original (bases c w legal) w.auth.ivk) w) (withOperations c) w) w authInitial) w) w) w)
    (withOperations c) w initial senderInitial receiverInitial slot offset
  have x := coordinate ⟨0,by decide⟩
  have y := coordinate ⟨1,by decide⟩
  apply congrArg₂ Group.Point.mk
  · simpa only [VariableWindowColumns449.columnPoint,SubgroupSeedCompletion203.fieldPoint,
      UserSubgroupSeed352.value,Nat.add_zero,if_pos rfl] using x
  · simpa only [VariableWindowColumns449.columnPoint,SubgroupSeedCompletion203.fieldPoint,
      UserSubgroupSeed352.value,show ¬(1:Nat)=0 from by decide,if_false,if_pos rfl] using y

theorem base (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (bound : index<2) :
    VariableWindowColumns449.columnPoint
      (assignment original c w legal authInitial initial senderInitial receiverInitial) (1504+16*index)=
    model.coordinates (bases c w legal index) := by
  have cases : index=0 ∨ index=1 := by omega
  rcases cases with rfl|rfl
  · rw [bases,if_pos rfl,AuthorizationGroupDomain445.coordinates]
    exact sender_point original c w legal authInitial initial senderInitial receiverInitial ⟨0,by decide⟩
  · rw [bases,if_neg (by decide),AuthorizationGroupDomain445.coordinates]
    exact sender_point original c w legal authInitial initial senderInitial receiverInitial ⟨2,by decide⟩

theorem bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (bound : index<252) :
    assignment original c w legal authInitial initial senderInitial receiverInitial (2000+index)=
      if (encodeBits 252 w.auth.ivk)[index]?.getD false then 1 else 0 := by
  have bits := SharedIvkCanonical390.ivk_bits
    (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed (IvkInverseSeed426.seed (AuthorizationTraceSeed451.seed original (bases c w legal) w.auth.ivk) w) (withOperations c) w) w authInitial)
    (withOperations c) w initial senderInitial receiverInitial legal index bound
  simpa only [ScalarCanonicalNumeric388.bitAt,Nat.add_sub_cancel_left,BinaryComparison100.bit] using bits
end ShielddSecurity.AuthorizationTraceBindings458

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceBindings458.sender_point
#print axioms ShielddSecurity.AuthorizationTraceBindings458.sender_point

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceBindings458.base
#print axioms ShielddSecurity.AuthorizationTraceBindings458.base

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceBindings458.bits
#print axioms ShielddSecurity.AuthorizationTraceBindings458.bits
