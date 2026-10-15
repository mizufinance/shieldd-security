import ShielddSecurity.UserLeafNatural1229
import ShielddSecurity.UserPathWitness961
import ShielddSecurity.UserPathInputs962
import ShielddSecurity.VolumePathValues947
import ShielddSecurity.UserPathHash958C21
import ShielddSecurity.UserPathHash958C38
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserLeafMeaning963
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumePathAssignment942 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model SatisfiesAt
  PoseidonNatural192.hash Poseidon.hash6 userLeaf

def fields (asset : Nat) (user : User) : List Nat :=
  [user.address.diversified.x,user.address.diversified.y,
   user.address.transmission.x,user.address.transmission.y,asset,
   user.rnkDH.x,user.rnkDH.y,user.rnkCommitment,user.lifecycle]

theorem natural (c : Crypto) (asset : Nat) (user : User) :
    (userLeaf (BalanceBlindingDomain670.crypto c) asset user:F)=
      Poseidon.hash6 (RegistryNatural193.wide : Poseidon.Parameters F 6) 19 ((fields asset user).map (fun x => (x:F))) :=
  UserLeafNatural1229.natural c asset user

variable (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F)
theorem ports21 (rho : Nat → F) : UserPathHash958C21.inputs.map (eval rho)=[rho 1504,rho 1505,rho 1512,rho 1513,rho 6,rho 1520,rho 1521,rho 1528,rho 1529] := by
  simp [UserPathHash958C21.inputs,eval]
theorem values21 : UserPathHash958C21.inputs.map (eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial))=(fields w.asset w.sender).map (fun x => (x:F)) := by
  have x00 : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1504=(w.sender.address.diversified.x:F) :=
    UserPathWitness961.sender_coordinate original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨0,by decide⟩ ⟨0,by decide⟩
  have x01 : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1505=(w.sender.address.diversified.y:F) :=
    UserPathWitness961.sender_coordinate original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨0,by decide⟩ ⟨1,by decide⟩
  have x10 : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1512=(w.sender.address.transmission.x:F) :=
    UserPathWitness961.sender_coordinate original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨1,by decide⟩ ⟨0,by decide⟩
  have x11 : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1513=(w.sender.address.transmission.y:F) :=
    UserPathWitness961.sender_coordinate original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨1,by decide⟩ ⟨1,by decide⟩
  have x20 : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1520=(w.sender.rnkDH.x:F) :=
    UserPathWitness961.sender_coordinate original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨2,by decide⟩ ⟨0,by decide⟩
  have x21 : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1521=(w.sender.rnkDH.y:F) :=
    UserPathWitness961.sender_coordinate original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨2,by decide⟩ ⟨1,by decide⟩
  have commitment := (UserPathWitness961.commitments original u c w legal rkInitial authInitial initial senderInitial receiverInitial).1
  have lifecycle : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1529=(w.sender.lifecycle:F) :=
    UserPathInputs962.words original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1529 (by decide +kernel)
  rw [ports21,x00,x01,x10,x11,x20,x21,commitment,lifecycle,UserPathInputs962.asset original u c w legal rkInitial authInitial initial senderInitial receiverInitial]
  rfl
theorem hash21 : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C21.result=(userLeaf (BalanceBlindingDomain670.crypto c) w.asset w.sender:F) := by
  have zero := VolumePathValues947.zero original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have copied := VolumePathValues947.copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := VolumePathValues947.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have result := UserPathHash958C21.hash _ zero (copied.trans zero.symm) arithmetic
  rw [values21 original u c w legal rkInitial authInitial initial senderInitial receiverInitial] at result
  exact result.trans (natural c w.asset w.sender).symm
theorem ports38 (rho : Nat → F) : UserPathHash958C38.inputs.map (eval rho)=[rho 1742,rho 1743,rho 1750,rho 1751,rho 6,rho 1758,rho 1759,rho 1766,rho 1767] := by
  simp [UserPathHash958C38.inputs,eval]
theorem values38 : UserPathHash958C38.inputs.map (eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial))=(fields w.asset w.receiver).map (fun x => (x:F)) := by
  have x00 : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1742=(w.receiver.address.diversified.x:F) :=
    UserPathWitness961.receiver_coordinate original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨0,by decide⟩ ⟨0,by decide⟩
  have x01 : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1743=(w.receiver.address.diversified.y:F) :=
    UserPathWitness961.receiver_coordinate original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨0,by decide⟩ ⟨1,by decide⟩
  have x10 : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1750=(w.receiver.address.transmission.x:F) :=
    UserPathWitness961.receiver_coordinate original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨1,by decide⟩ ⟨0,by decide⟩
  have x11 : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1751=(w.receiver.address.transmission.y:F) :=
    UserPathWitness961.receiver_coordinate original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨1,by decide⟩ ⟨1,by decide⟩
  have x20 : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1758=(w.receiver.rnkDH.x:F) :=
    UserPathWitness961.receiver_coordinate original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨2,by decide⟩ ⟨0,by decide⟩
  have x21 : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1759=(w.receiver.rnkDH.y:F) :=
    UserPathWitness961.receiver_coordinate original u c w legal rkInitial authInitial initial senderInitial receiverInitial ⟨2,by decide⟩ ⟨1,by decide⟩
  have commitment := (UserPathWitness961.commitments original u c w legal rkInitial authInitial initial senderInitial receiverInitial).2
  have lifecycle : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1767=(w.receiver.lifecycle:F) :=
    UserPathInputs962.words original u c w legal rkInitial authInitial initial senderInitial receiverInitial 1767 (by decide +kernel)
  rw [ports38,x00,x01,x10,x11,x20,x21,commitment,lifecycle,UserPathInputs962.asset original u c w legal rkInitial authInitial initial senderInitial receiverInitial]
  rfl
theorem hash38 : eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) UserPathHash958C38.result=(userLeaf (BalanceBlindingDomain670.crypto c) w.asset w.receiver:F) := by
  have zero := VolumePathValues947.zero original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have copied := VolumePathValues947.copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := VolumePathValues947.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have result := UserPathHash958C38.hash _ zero (copied.trans zero.symm) arithmetic
  rw [values38 original u c w legal rkInitial authInitial initial senderInitial receiverInitial] at result
  exact result.trans (natural c w.asset w.receiver).symm
end ShielddSecurity.UserLeafMeaning963

set_option pp.all true in
#check @ShielddSecurity.UserLeafMeaning963.natural
#print axioms ShielddSecurity.UserLeafMeaning963.natural

set_option pp.all true in
#check @ShielddSecurity.UserLeafMeaning963.ports21
#print axioms ShielddSecurity.UserLeafMeaning963.ports21

set_option pp.all true in
#check @ShielddSecurity.UserLeafMeaning963.values21
#print axioms ShielddSecurity.UserLeafMeaning963.values21

set_option pp.all true in
#check @ShielddSecurity.UserLeafMeaning963.hash21
#print axioms ShielddSecurity.UserLeafMeaning963.hash21

set_option pp.all true in
#check @ShielddSecurity.UserLeafMeaning963.ports38
#print axioms ShielddSecurity.UserLeafMeaning963.ports38

set_option pp.all true in
#check @ShielddSecurity.UserLeafMeaning963.values38
#print axioms ShielddSecurity.UserLeafMeaning963.values38

set_option pp.all true in
#check @ShielddSecurity.UserLeafMeaning963.hash38
#print axioms ShielddSecurity.UserLeafMeaning963.hash38
