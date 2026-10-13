import ShielddSecurity.UserPointDomain351
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserSubgroupSeed352
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def start (receiver : Bool) : Nat := if receiver then 1742 else 1504

def value (user : User) (initial : Fin 3 → Group.Point F) (slot : Fin 3) (offset : Nat) : F :=
  if offset=0 then ((UserPointDomain351.point user slot).x:F)
  else if offset=1 then ((UserPointDomain351.point user slot).y:F)
  else if offset=2 then (initial slot).x
  else if offset=3 then (initial slot).y
  else if offset<7 then CompilerSubgroupArithmetic79.hints (CapturedFirstSubgroup81.d:F) (initial slot) (offset-4)
  else ((UserPointDomain351.point user slot).x:F)⁻¹

def seed (original : Nat → F) (w : TransferSem.Witness)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat) : F :=
  if inside : 1504≤column ∧ column<1528 then
    value w.sender senderInitial ⟨(column-1504)/8,by omega⟩ ((column-1504)%8)
  else if inside : 1742≤column ∧ column<1766 then
    value w.receiver receiverInitial ⟨(column-1742)/8,by omega⟩ ((column-1742)%8)
  else original column

theorem outside (original : Nat → F) (w : TransferSem.Witness)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (column : Nat)
    (sender : ¬(1504≤column ∧ column<1528)) (receiver : ¬(1742≤column ∧ column<1766)) :
    seed original w senderInitial receiverInitial column=original column := by
  simp only [seed,dif_neg sender,dif_neg receiver]

theorem sender_value (original : Nat → F) (w : TransferSem.Witness)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (slot : Fin 3) (offset : Fin 8) :
    seed original w senderInitial receiverInitial (1504+8*slot.val+offset.val)=value w.sender senderInitial slot offset.val := by
  have groupBound := slot.isLt
  have offsetBound := offset.isLt
  have inside : 1504≤1504+8*slot.val+offset.val ∧ 1504+8*slot.val+offset.val<1528 := by omega
  simp only [seed,dif_pos inside]
  have difference : 1504+8*slot.val+offset.val-1504=8*slot.val+offset.val := by omega
  have division : (8*slot.val+offset.val)/8=slot.val := by omega
  have remainder : (8*slot.val+offset.val)%8=offset.val := by omega
  apply congrArg₂ (value w.sender senderInitial)
  · apply Fin.ext
    change (1504+8*slot.val+offset.val-1504)/8=slot.val
    rw [difference,division]
  · rw [difference,remainder]

theorem receiver_value (original : Nat → F) (w : TransferSem.Witness)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (slot : Fin 3) (offset : Fin 8) :
    seed original w senderInitial receiverInitial (1742+8*slot.val+offset.val)=value w.receiver receiverInitial slot offset.val := by
  have groupBound := slot.isLt
  have offsetBound := offset.isLt
  have outside : ¬(1504≤1742+8*slot.val+offset.val ∧1742+8*slot.val+offset.val<1528) := by omega
  have inside : 1742≤1742+8*slot.val+offset.val ∧1742+8*slot.val+offset.val<1766 := by omega
  simp only [seed,dif_neg outside,dif_pos inside]
  have difference : 1742+8*slot.val+offset.val-1742=8*slot.val+offset.val := by omega
  have division : (8*slot.val+offset.val)/8=slot.val := by omega
  have remainder : (8*slot.val+offset.val)%8=offset.val := by omega
  apply congrArg₂ (value w.receiver receiverInitial)
  · apply Fin.ext
    change (1742+8*slot.val+offset.val-1742)/8=slot.val
    rw [difference,division]
  · rw [difference,remainder]

theorem sender_inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (slot : Fin 3) :
    seed original w senderInitial receiverInitial (1504+8*slot.val)*
      seed original w senderInitial receiverInitial (1504+8*slot.val+7)=1 := by
  have first := sender_value original w senderInitial receiverInitial slot ⟨0,by decide⟩
  have inverse := sender_value original w senderInitial receiverInitial slot ⟨7,by decide⟩
  rw [Nat.add_zero] at first
  rw [first,inverse]
  exact UserPointDomain351.inverse_equation c w w.sender legal.2.1.2.1 slot

theorem receiver_inverse (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (slot : Fin 3) :
    seed original w senderInitial receiverInitial (1742+8*slot.val)*
      seed original w senderInitial receiverInitial (1742+8*slot.val+7)=1 := by
  have first := receiver_value original w senderInitial receiverInitial slot ⟨0,by decide⟩
  have inverse := receiver_value original w senderInitial receiverInitial slot ⟨7,by decide⟩
  rw [Nat.add_zero] at first
  rw [first,inverse]
  exact UserPointDomain351.inverse_equation c w w.receiver legal.2.1.2.2.1 slot
end ShielddSecurity.UserSubgroupSeed352

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupSeed352.start
#print axioms ShielddSecurity.UserSubgroupSeed352.start

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupSeed352.value
#print axioms ShielddSecurity.UserSubgroupSeed352.value

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupSeed352.seed
#print axioms ShielddSecurity.UserSubgroupSeed352.seed

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupSeed352.outside
#print axioms ShielddSecurity.UserSubgroupSeed352.outside

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupSeed352.sender_value
#print axioms ShielddSecurity.UserSubgroupSeed352.sender_value

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupSeed352.receiver_value
#print axioms ShielddSecurity.UserSubgroupSeed352.receiver_value

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupSeed352.sender_inverse
#print axioms ShielddSecurity.UserSubgroupSeed352.sender_inverse

set_option pp.all true in
#check @ShielddSecurity.UserSubgroupSeed352.receiver_inverse
#print axioms ShielddSecurity.UserSubgroupSeed352.receiver_inverse
