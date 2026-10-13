import ShielddSecurity.UserNonidentityConstruction360
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.UserPathSeed361
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def seed (original : Nat → F) (w : TransferSem.Witness) (column : Nat) : F :=
  if column=1528 then (w.sender.rnkCommitment:F)
  else if column=1766 then (w.receiver.rnkCommitment:F)
  else if 1531≤column ∧ column<1579 then
    (w.sender.siblings ⟨((column-1531)/3)%16,Nat.mod_lt _ (by decide)⟩
      ⟨(column-1531)%3,Nat.mod_lt _ (by decide)⟩:F)
  else if 1769≤column ∧ column<1817 then
    (w.receiver.siblings ⟨((column-1769)/3)%16,Nat.mod_lt _ (by decide)⟩
      ⟨(column-1769)%3,Nat.mod_lt _ (by decide)⟩:F)
  else original column

theorem commitments (original : Nat → F) (w : TransferSem.Witness) :
    seed original w 1528=(w.sender.rnkCommitment:F) ∧ seed original w 1766=(w.receiver.rnkCommitment:F) := by
  constructor <;> rfl

theorem outside (original : Nat → F) (w : TransferSem.Witness) (column : Nat)
    (sender : column≠1528) (receiver : column≠1766)
    (senderPath : ¬(1531≤column ∧ column<1579)) (receiverPath : ¬(1769≤column ∧ column<1817)) :
    seed original w column=original column := by
  simp only [seed,if_neg sender,if_neg receiver,if_neg senderPath,if_neg receiverPath]

theorem sender_siblings (original : Nat → F) (w : TransferSem.Witness) (level : Fin 16) (slot : Fin 3) :
    seed original w (1531+3*level.val+slot.val)=(w.sender.siblings level slot:F) := by
  have levelBound := level.isLt
  have slotBound := slot.isLt
  have first : 1531+3*level.val+slot.val≠1528 := by omega
  have second : 1531+3*level.val+slot.val≠1766 := by omega
  have inside : 1531≤1531+3*level.val+slot.val ∧ 1531+3*level.val+slot.val<1579 := by omega
  simp only [seed,if_neg first,if_neg second,if_pos inside]
  have difference : 1531+3*level.val+slot.val-1531=3*level.val+slot.val := by omega
  have division : (3*level.val+slot.val)/3=level.val := by omega
  have remainder : (3*level.val+slot.val)%3=slot.val := by omega
  apply congrArg (fun value : Nat => (value:F))
  apply congrArg₂ w.sender.siblings
  · apply Fin.ext
    change ((1531+3*level.val+slot.val-1531)/3)%16=level.val
    rw [difference,division,Nat.mod_eq_of_lt levelBound]
  · apply Fin.ext
    change (1531+3*level.val+slot.val-1531)%3=slot.val
    rw [difference,remainder]

theorem receiver_siblings (original : Nat → F) (w : TransferSem.Witness) (level : Fin 16) (slot : Fin 3) :
    seed original w (1769+3*level.val+slot.val)=(w.receiver.siblings level slot:F) := by
  have levelBound := level.isLt
  have slotBound := slot.isLt
  have first : 1769+3*level.val+slot.val≠1528 := by omega
  have second : 1769+3*level.val+slot.val≠1766 := by omega
  have outside : ¬(1531≤1769+3*level.val+slot.val ∧ 1769+3*level.val+slot.val<1579) := by omega
  have inside : 1769≤1769+3*level.val+slot.val ∧ 1769+3*level.val+slot.val<1817 := by omega
  simp only [seed,if_neg first,if_neg second,if_neg outside,if_pos inside]
  have difference : 1769+3*level.val+slot.val-1769=3*level.val+slot.val := by omega
  have division : (3*level.val+slot.val)/3=level.val := by omega
  have remainder : (3*level.val+slot.val)%3=slot.val := by omega
  apply congrArg (fun value : Nat => (value:F))
  apply congrArg₂ w.receiver.siblings
  · apply Fin.ext
    change ((1769+3*level.val+slot.val-1769)/3)%16=level.val
    rw [difference,division,Nat.mod_eq_of_lt levelBound]
  · apply Fin.ext
    change (1769+3*level.val+slot.val-1769)%3=slot.val
    rw [difference,remainder]

theorem canonical_append (left right : List Nat) : fieldsCanonical (left++right) ↔ fieldsCanonical left ∧ fieldsCanonical right := by
  simp only [fieldsCanonical,List.mem_append,or_imp,forall_and]

theorem users_canonical (w : TransferSem.Witness) (canonical : CanonicalWitness w) :
    fieldsCanonical (userFields w.sender) ∧ fieldsCanonical (userFields w.receiver) := by
  simp only [CanonicalWitness,canonical_append] at canonical
  rcases canonical with ⟨⟨⟨⟨⟨⟨⟨⟨_,_⟩,_⟩,_⟩,sender⟩,receiver⟩,_⟩,_⟩,_⟩
  exact ⟨sender,receiver⟩

theorem commitments_bound (w : TransferSem.Witness) (canonical : CanonicalWitness w) :
    w.sender.rnkCommitment<TransferCore.fieldModulus ∧ w.receiver.rnkCommitment<TransferCore.fieldModulus := by
  have users := users_canonical w canonical
  exact ⟨users.1 _ (by simp [userFields]),users.2 _ (by simp [userFields])⟩

theorem sibling_bound (user : User) (canonical : fieldsCanonical (userFields user)) (level : Fin 16) (slot : Fin 3) :
    user.siblings level slot<TransferCore.fieldModulus := by
  have member : user.siblings level slot ∈ pathFields user.siblings :=
    List.mem_flatMap.mpr ⟨level,by simp,List.mem_map.mpr ⟨slot,by simp,rfl⟩⟩
  exact canonical _ (List.mem_append_right _ member)

theorem recovered_commitments (original : Nat → F) (w : TransferSem.Witness) (canonical : CanonicalWitness w) :
    representation.value (seed original w 1528)=w.sender.rnkCommitment ∧
    representation.value (seed original w 1766)=w.receiver.rnkCommitment := by
  have bound := commitments_bound w canonical
  rw [(commitments original w).1,(commitments original w).2,
    RegistryNaturalSeed298.represented_nat _ bound.1,RegistryNaturalSeed298.represented_nat _ bound.2]
  exact ⟨rfl,rfl⟩

theorem recovered_sender_path (original : Nat → F) (w : TransferSem.Witness) (canonical : CanonicalWitness w)
    (level : Fin 16) (slot : Fin 3) :
    representation.value (seed original w (1531+3*level.val+slot.val))=w.sender.siblings level slot := by
  rw [sender_siblings,RegistryNaturalSeed298.represented_nat _ (sibling_bound w.sender (users_canonical w canonical).1 level slot)]

theorem recovered_receiver_path (original : Nat → F) (w : TransferSem.Witness) (canonical : CanonicalWitness w)
    (level : Fin 16) (slot : Fin 3) :
    representation.value (seed original w (1769+3*level.val+slot.val))=w.receiver.siblings level slot := by
  rw [receiver_siblings,RegistryNaturalSeed298.represented_nat _ (sibling_bound w.receiver (users_canonical w canonical).2 level slot)]
end ShielddSecurity.UserPathSeed361

set_option pp.all true in
#check @ShielddSecurity.UserPathSeed361.seed
#print axioms ShielddSecurity.UserPathSeed361.seed

set_option pp.all true in
#check @ShielddSecurity.UserPathSeed361.commitments
#print axioms ShielddSecurity.UserPathSeed361.commitments

set_option pp.all true in
#check @ShielddSecurity.UserPathSeed361.outside
#print axioms ShielddSecurity.UserPathSeed361.outside

set_option pp.all true in
#check @ShielddSecurity.UserPathSeed361.sender_siblings
#print axioms ShielddSecurity.UserPathSeed361.sender_siblings

set_option pp.all true in
#check @ShielddSecurity.UserPathSeed361.receiver_siblings
#print axioms ShielddSecurity.UserPathSeed361.receiver_siblings

set_option pp.all true in
#check @ShielddSecurity.UserPathSeed361.canonical_append
#print axioms ShielddSecurity.UserPathSeed361.canonical_append

set_option pp.all true in
#check @ShielddSecurity.UserPathSeed361.users_canonical
#print axioms ShielddSecurity.UserPathSeed361.users_canonical

set_option pp.all true in
#check @ShielddSecurity.UserPathSeed361.commitments_bound
#print axioms ShielddSecurity.UserPathSeed361.commitments_bound

set_option pp.all true in
#check @ShielddSecurity.UserPathSeed361.sibling_bound
#print axioms ShielddSecurity.UserPathSeed361.sibling_bound

set_option pp.all true in
#check @ShielddSecurity.UserPathSeed361.recovered_commitments
#print axioms ShielddSecurity.UserPathSeed361.recovered_commitments

set_option pp.all true in
#check @ShielddSecurity.UserPathSeed361.recovered_sender_path
#print axioms ShielddSecurity.UserPathSeed361.recovered_sender_path

set_option pp.all true in
#check @ShielddSecurity.UserPathSeed361.recovered_receiver_path
#print axioms ShielddSecurity.UserPathSeed361.recovered_receiver_path
