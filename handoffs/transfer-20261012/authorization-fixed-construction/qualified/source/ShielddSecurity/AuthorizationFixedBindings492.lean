import ShielddSecurity.AuthorizationFixedSeed487
import ShielddSecurity.AuthorizationDhConstruction474
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationFixedBindings492
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationFixedSeed487 (seed assignment window)

theorem point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (bound : index<126) :
    VariableWindowColumns449.columnPoint (assignment original c w legal authInitial initial senderInitial receiverInitial)
      (4019+2*index)=(window w.auth.randomizer index).output := by
  have x := AuthorizationFixedSeed487.completed_hint original c w legal authInitial initial senderInitial receiverInitial
    (4019+2*index) (by omega)
  have y := AuthorizationFixedSeed487.completed_hint original c w legal authInitial initial senderInitial receiverInitial
    (4019+2*index+1) (by omega)
  have coordinates := congrArg₂ Group.Point.mk x y
  exact coordinates.trans (AuthorizationFixedSeed487.point original w.auth.randomizer index bound)

theorem bits (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (bound : index<252) :
    assignment original c w legal authInitial initial senderInitial receiverInitial (3767+index)=
      if (encodeBits 252 w.auth.randomizer)[index]?.getD false then 1 else 0 := by
  let chosen := AuthorizationFixedDomain485.withGenerator c
  let inner := IvkInverseSeed426.seed (AuthorizationTraceSeed451.seed
    (AuthorizationDhSeed473.seed (seed original w.auth.randomizer) chosen w legal)
    (AuthorizationTraceAssignment457.bases chosen w legal) w.auth.ivk) w
  have result := SharedScalarCanonical396.all_bits
    (AuthorizationPointSeed405.seed (AuthorizationSharedSeed416.seed inner (ConcreteAuthorizationCrypto430.withOperations chosen) w) w authInitial)
    (ConcreteAuthorizationCrypto430.withOperations chosen) w initial senderInitial receiverInitial legal ⟨0,by decide⟩ index bound
  have value : SharedScalarCanonical396.numbers w ⟨0,by decide⟩=w.auth.randomizer := by
    change EncodedWordBits375.value w 3766=w.auth.randomizer
    simp only [EncodedWordBits375.value,AuthScalarSeed366.values,List.mem_cons,List.mem_singleton,
      show ¬(3766:Nat)=1994 from by decide,show ¬(3766:Nat)=1995 from by decide,
      or_self,or_false,or_true,false_or,true_or,if_true,AuthScalarSeed366.value,if_false]
  rw [value] at result
  exact result

theorem arithmetic (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original c w legal authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 :=
  AuthorizationDhSeed473.arithmetic (seed original w.auth.randomizer) (AuthorizationFixedDomain485.withGenerator c)
    w legal authInitial initial senderInitial receiverInitial

theorem copied (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    assignment original c w legal authInitial initial senderInitial receiverInitial copy=1 :=
  AuthorizationDhSeed473.copied (seed original w.auth.randomizer) (AuthorizationFixedDomain485.withGenerator c)
    w legal authInitial initial senderInitial receiverInitial

def Earlier (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) : Prop :=
  AuthorizationDhSeed473.Earlier (seed original w.auth.randomizer) (AuthorizationFixedDomain485.withGenerator c)
    w legal authInitial initial senderInitial receiverInitial ∧
  CapturedDhInverse472.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial)

theorem retained (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (AuthorizationFixedDomain485.crypto c) w) :
    ∃ authInitial : Group.Point F, ∃ senderInitial : Fin 3 → Group.Point F,
    ∃ receiverInitial : Fin 3 → Group.Point F, ∃ initial : Fin 4 → Group.Point F,
      Earlier original c w legal authInitial initial senderInitial receiverInitial :=
  AuthorizationDhConstruction474.legal_completed (seed original w.auth.randomizer) (AuthorizationFixedDomain485.withGenerator c) w legal
end ShielddSecurity.AuthorizationFixedBindings492

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedBindings492.point
#print axioms ShielddSecurity.AuthorizationFixedBindings492.point

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedBindings492.bits
#print axioms ShielddSecurity.AuthorizationFixedBindings492.bits

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedBindings492.arithmetic
#print axioms ShielddSecurity.AuthorizationFixedBindings492.arithmetic

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedBindings492.copied
#print axioms ShielddSecurity.AuthorizationFixedBindings492.copied

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedBindings492.Earlier
#print axioms ShielddSecurity.AuthorizationFixedBindings492.Earlier

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFixedBindings492.retained
#print axioms ShielddSecurity.AuthorizationFixedBindings492.retained
