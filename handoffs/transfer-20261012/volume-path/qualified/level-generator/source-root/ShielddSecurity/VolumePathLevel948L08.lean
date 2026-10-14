-- GENERATED from maintained path level composition; do not edit.
import ShielddSecurity.VolumePathSelector945L08
import ShielddSecurity.VolumePathValues947
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumePathLevel948L08
open Compiler CompilerAssertionBlock51 TransferSem
open CapturedInitial73419Generic01 (p copy)
attribute [local irreducible] SatisfiesAt ConcreteRegistrySharedEncoding294.model
  VolumePathAssignment942.assignment VolumePathMeaning946.value PoseidonNatural192.hash Poseidon.hash6 volumeState

theorem generic_hash {G : Type} [Field G] [CharP G p] (rho : Nat → G)
    (one : rho 0=1) (copied : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (low high : Bool)
    (node s0 s1 s2 : G)
    (low_value : rho 8476=BooleanHints207.bitValue low) (high_value : rho 8477=BooleanHints207.bitValue high)
    (previous : eval rho VolumePathHash931C132.result=node)
    (first : rho 8412=s0) (second : rho 8413=s1) (third : rho 8414=s2) :
    eval rho VolumePathHash931C133.result=Poseidon.hash6 (Poseidon.castParameters VolumePathHash931C133.parameters) 1
      ([(9:G)]++QuaternarySelector944.children
        (if high then (if low then 3 else 2) else (if low then 1 else 0)) node s0 s1 s2) := by
  have result := VolumePathHash931C133.hash rho one (copied.trans one.symm) arithmetic
  rw [VolumePathSelector945L08.input_values rho one arithmetic low high low_value high_value,previous,first,second,third] at result
  exact result

open ConcreteJubjubField01
open VolumePathAssignment942 (assignment)
variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)

theorem result (previous : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePathHash931C132.result=
    (VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w 8:F)) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumePathHash931C133.result=
      (VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w 9:F) := by
  have first : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8412=(VolumePathMeaning946.siblings w 8 0:F) := by
    simpa only [VolumePathMeaning946.siblings,dif_pos (show 8<24 by decide)] using
      VolumePathAssignment942.sibling original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨8,by decide⟩ 0
  have second : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8413=(VolumePathMeaning946.siblings w 8 1:F) := by
    simpa only [VolumePathMeaning946.siblings,dif_pos (show 8<24 by decide)] using
      VolumePathAssignment942.sibling original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨8,by decide⟩ 1
  have third : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 8414=(VolumePathMeaning946.siblings w 8 2:F) := by
    simpa only [VolumePathMeaning946.siblings,dif_pos (show 8<24 by decide)] using
      VolumePathAssignment942.sibling original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨8,by decide⟩ 2
  have joined := generic_hash (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) (VolumePathValues947.zero original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (VolumePathValues947.copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial) (VolumePathValues947.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    ((encodeBits 48 w.volume.priorPosition)[16]?.getD false)
    ((encodeBits 48 w.volume.priorPosition)[17]?.getD false) _ _ _ _
    (VolumePathBits943.bits original u c w legal rkInitial authInitial initial senderInitial receiverInitial 16 (by decide))
    (VolumePathBits943.bits original u c w legal rkInitial authInitial initial senderInitial receiverInitial 17 (by decide)) previous first second third
  rw [QuaternarySelector944.encoded_slot w.volume.priorPosition 8 (by decide)] at joined
  rw [show 9=8+1 from rfl,VolumePathMeaning946.successor]
  have natural := VolumePathMeaning946.natural_hash c 8 (w.volume.priorPosition/4^8%4)
    (VolumePathMeaning946.value (BalanceBlindingDomain670.crypto c) w 8)
    (VolumePathMeaning946.siblings w 8 0) (VolumePathMeaning946.siblings w 8 1)
    (VolumePathMeaning946.siblings w 8 2)
  exact joined.trans natural.symm
end ShielddSecurity.VolumePathLevel948L08

set_option pp.all true in
#check @ShielddSecurity.VolumePathLevel948L08.generic_hash
#print axioms ShielddSecurity.VolumePathLevel948L08.generic_hash

set_option pp.all true in
#check @ShielddSecurity.VolumePathLevel948L08.result
#print axioms ShielddSecurity.VolumePathLevel948L08.result
