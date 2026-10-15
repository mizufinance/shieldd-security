-- GENERATED from maintained path level composition; do not edit.
import ShielddSecurity.UserPathSelector964RL04
import ShielddSecurity.VolumePathValues947
import ShielddSecurity.UserPathWitness961
import ShielddSecurity.UserPathInputs962
import ShielddSecurity.UserTreeMeaning965
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathLevel966RL04
open Compiler CompilerAssertionBlock51 TransferSem
open CapturedInitial73419Generic01 (p copy)
attribute [local irreducible] SatisfiesAt ConcreteRegistrySharedEncoding294.model
  VolumePathAssignment942.assignment UserTreeMeaning965.value PoseidonNatural192.hash Poseidon.hash6 userLeaf

theorem generic_hash {G : Type} [Field G] [CharP G p] (rho : Nat → G)
    (one : rho 0=1) (copied : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (low high : Bool)
    (node s0 s1 s2 : G)
    (low_value : rho 1825=BooleanHints207.bitValue low) (high_value : rho 1826=BooleanHints207.bitValue high)
    (previous : eval rho UserPathHash958C42.result=node)
    (first : rho 1781=s0) (second : rho 1782=s1) (third : rho 1783=s2) :
    eval rho UserPathHash958C43.result=Poseidon.hash6 (Poseidon.castParameters UserPathHash958C43.parameters) 3
      ([(5:G)]++QuaternarySelector944.children
        (if high then (if low then 3 else 2) else (if low then 1 else 0)) node s0 s1 s2) := by
  have result := UserPathHash958C43.hash rho one (copied.trans one.symm) arithmetic
  rw [UserPathSelector964RL04.input_values rho one arithmetic low high low_value high_value,previous,first,second,third] at result
  exact result

open ConcreteJubjubField01
open VolumePathAssignment942 (assignment)
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem result (previous : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C42.result=
    (UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.receiver 4:F)) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C43.result=
      (UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.receiver 5:F) := by
  have first : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1781=(UserTreeMeaning965.siblings w.receiver 4 0:F) := by
    simpa only [UserTreeMeaning965.siblings,dif_pos (show 4<16 by decide)] using
      UserPathWitness961.receiver_siblings original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨4,by decide⟩ 0
  have second : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1782=(UserTreeMeaning965.siblings w.receiver 4 1:F) := by
    simpa only [UserTreeMeaning965.siblings,dif_pos (show 4<16 by decide)] using
      UserPathWitness961.receiver_siblings original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨4,by decide⟩ 1
  have third : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1783=(UserTreeMeaning965.siblings w.receiver 4 2:F) := by
    simpa only [UserTreeMeaning965.siblings,dif_pos (show 4<16 by decide)] using
      UserPathWitness961.receiver_siblings original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨4,by decide⟩ 2
  have joined := generic_hash (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) (VolumePathValues947.zero original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (VolumePathValues947.copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial) (VolumePathValues947.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    ((encodeBits 32 w.receiver.position)[8]?.getD false)
    ((encodeBits 32 w.receiver.position)[9]?.getD false) _ _ _ _
    (UserPathInputs962.receiver_bits original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8 (by decide))
    (UserPathInputs962.receiver_bits original u c w legal rkInitial authInitial initial senderInitial receiverInitial 9 (by decide)) previous first second third
  rw [UserPathInputs962.encoded_slot w.receiver.position 4 (by decide)] at joined
  rw [show 5=4+1 from rfl,UserTreeMeaning965.successor]
  have natural := UserTreeMeaning965.natural_hash c 4 (w.receiver.position/4^4%4)
    (UserTreeMeaning965.value (BalanceBlindingDomain670.crypto c) w.asset w.receiver 4)
    (UserTreeMeaning965.siblings w.receiver 4 0) (UserTreeMeaning965.siblings w.receiver 4 1)
    (UserTreeMeaning965.siblings w.receiver 4 2)
  exact joined.trans natural.symm
end ShielddSecurity.UserPathLevel966RL04

set_option pp.all true in
#check @ShielddSecurity.UserPathLevel966RL04.generic_hash
#print axioms ShielddSecurity.UserPathLevel966RL04.generic_hash

set_option pp.all true in
#check @ShielddSecurity.UserPathLevel966RL04.result
#print axioms ShielddSecurity.UserPathLevel966RL04.result
