import ShielddSecurity.MerklePath33Meaning
import ShielddSecurity.MerkleQuaternary30
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleOrdered34
open Compiler Poseidon
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F]
def orderedStep (rho : Nat → F) (bits : Fin 32 → Bool) (level : Fin 16) (node : F) : F :=
  let children := MerkleQuaternary30.children
    (bits ⟨2*level.val,by have h:=level.isLt;omega⟩)
    (bits ⟨2*level.val+1,by have h:=level.isLt;omega⟩) node
    (rho (136+3*level.val)) (rho (137+3*level.val)) (rho (138+3*level.val))
  Poseidon.hash6 (castParameters TransferPoseidonCall04Shared01.parameters) 2
    [((level.val+1 : Nat) : F),children 0,children 1,children 2,children 3]
def root (rho : Nat → F) (bits : Fin 32 → Bool) : Nat → F
  | 0 => MerkleInputMeaning28.registryMeaning rho
  | n+1 => orderedStep rho bits ⟨n%16,Nat.mod_lt n (by decide)⟩ (root rho bits n)
variable [CharP F p]
theorem exists_bits (rho : Nat → F) (sat : Satisfies rho MerkleBits29.actualRows) :
    ∃ bits : Fin 32 → Bool,∀ i : Fin 32,rho (184+i.val)=MerkleQuaternary30.boolValue (bits i) := by
  have each (i : Fin 32) : ∃ bit : Bool,rho (184+i.val)=MerkleQuaternary30.boolValue bit :=
    MerkleQuaternary30.encoded _ (MerkleBits29.bits_sound rho sat i)
  exact ⟨fun i => Classical.choose (each i),fun i => Classical.choose_spec (each i)⟩
omit [CharP F p] in
theorem first_step (rho : Nat → F) (bits : Fin 32 → Bool)
    (encoding : ∀ i : Fin 32,rho (184+i.val)=MerkleQuaternary30.boolValue (bits i)) :
    MerkleInputMeaning28.pathMeaning rho=orderedStep rho bits ⟨0,by decide⟩ (MerkleInputMeaning28.registryMeaning rho) := by
  have low := encoding ⟨0,by decide⟩
  have high := encoding ⟨1,by decide⟩
  change rho 184=_ at low
  change rho 185=_ at high
  unfold MerkleInputMeaning28.pathMeaning orderedStep
  rw [low,high,MerkleQuaternary30.formula_boolean]
  simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.cast_one,MerkleHash27R0Data.parameters]
omit [CharP F p] in
theorem later_step (i : Fin 15) (rho : Nat → F) (bits : Fin 32 → Bool) (node : F)
    (encoding : ∀ j : Fin 32,rho (184+j.val)=MerkleQuaternary30.boolValue (bits j)) :
    MerkleFamily32Whole.next i rho node=orderedStep rho bits ⟨i.val+1,by have h:=i.isLt;omega⟩ node := by
  have low := encoding ⟨2*(i.val+1),by have h:=i.isLt;omega⟩
  have high := encoding ⟨2*(i.val+1)+1,by have h:=i.isLt;omega⟩
  have highColumn : 184+(2*(i.val+1)+1)=185+2*(i.val+1) := by omega
  rw [highColumn] at high
  unfold MerkleFamily32Whole.next orderedStep
  rw [low,high,MerkleQuaternary30.formula_boolean]
omit [CharP F p] in
theorem meaning_eq (rho : Nat → F) (bits : Fin 32 → Bool)
    (encoding : ∀ i : Fin 32,rho (184+i.val)=MerkleQuaternary30.boolValue (bits i))
    (n : Nat) (bound : n≤15) : MerklePath33Meaning.meaning rho n=root rho bits (n+1) := by
  induction n with
  | zero => exact first_step rho bits encoding
  | succ n ih =>
    have below : n<15 := by omega
    change MerkleFamily32Whole.next ⟨n%15,Nat.mod_lt n (by decide)⟩ rho (MerklePath33Meaning.meaning rho n)=
      orderedStep rho bits ⟨(n+1)%16,Nat.mod_lt (n+1) (by decide)⟩ (root rho bits (n+1))
    rw [ih (by omega),later_step _ rho bits _ encoding]
    have eq : (⟨n%15+1,by have h:=Nat.mod_lt n (by decide : 0<15);omega⟩ : Fin 16)=
      ⟨(n+1)%16,Nat.mod_lt (n+1) (by decide)⟩ := by
      apply Fin.ext
      simp only [Nat.mod_eq_of_lt below,Nat.mod_eq_of_lt (show n+1<16 by omega)]
    rw [eq]
theorem arbitrary (rho : Nat → F) (one : rho 0=1)
    (prior : Satisfies rho MerkleHash27Whole.priorRows) (first : Satisfies rho MerkleHash27Whole.selectedRows)
    (rest : Satisfies rho (MerklePath33.rows (F:=F))) (bitsRows : Satisfies rho MerkleBits29.actualRows) :
    ∃ bits : Fin 32 → Bool,(∀ i : Fin 32,rho (184+i.val)=MerkleQuaternary30.boolValue (bits i)) ∧
      eval rho MerklePath33AnchorData.output=root rho bits 16 := by
  obtain ⟨bits,encoding⟩ := exists_bits rho bitsRows
  refine ⟨bits,encoding,?_⟩
  rw [MerklePath33Meaning.arbitrary rho one prior first rest,meaning_eq rho bits encoding 15 (by decide)]
theorem anchor_sound (rho : Nat → F) (one : rho 0=1)
    (prior : Satisfies rho MerkleHash27Whole.priorRows) (first : Satisfies rho MerkleHash27Whole.selectedRows)
    (rest : Satisfies rho (MerklePath33.rows (F:=F))) (bitsRows : Satisfies rho MerkleBits29.actualRows)
    (anchor : Satisfies rho [MerklePath33AnchorData.anchor]) :
    ∃ bits : Fin 32 → Bool,(∀ i : Fin 32,rho (184+i.val)=MerkleQuaternary30.boolValue (bits i)) ∧ rho 4=root rho bits 16 := by
  obtain ⟨bits,encoding⟩ := exists_bits rho bitsRows
  refine ⟨bits,encoding,?_⟩
  rw [MerklePath33Meaning.anchor_sound rho one prior first rest anchor,meaning_eq rho bits encoding 15 (by decide)]
theorem total (base : Nat → F) (n : Nat) (bound : n<2^32) (position : base 135=(n:F))
    (one : base 0=1) (linked : base copy=base 0) :
    ∃ bits : Fin 32 → Bool,Satisfies (MerklePath33Frame.final base n) MerklePath33Frame.priorRows ∧
      Satisfies (MerklePath33Frame.final base n) (MerklePath33.rows (F:=F)) ∧
      (∀ i : Fin 32,MerklePath33Frame.final base n (184+i.val)=MerkleQuaternary30.boolValue (bits i)) ∧
      eval (MerklePath33Frame.final base n) MerklePath33AnchorData.output=root (MerklePath33Frame.final base n) bits 16 := by
  have done := MerklePath33Frame.final_rows base n bound position one linked
  have bitsRows : Satisfies (MerklePath33Frame.final base n) MerkleBits29.actualRows :=
    fun row member => done.1 row (List.mem_append_right _ member)
  have prior : Satisfies (MerklePath33Frame.final base n) MerkleHash27Whole.priorRows :=
    fun row member => done.1 row (List.mem_append_left _ (List.mem_append_left _ member))
  have first : Satisfies (MerklePath33Frame.final base n) MerkleHash27Whole.selectedRows :=
    fun row member => done.1 row (List.mem_append_left _ (List.mem_append_right _ member))
  have oneFinal : MerklePath33Frame.final base n 0=1 :=
    (MerklePath33Frame.final_outside base n 0 (Or.inl ⟨by decide,Or.inl (by decide)⟩)).trans one
  obtain ⟨bits,encoding,value⟩ := arbitrary _ oneFinal prior first done.2 bitsRows
  exact ⟨bits,done.1,done.2,encoding,value⟩
end ShielddSecurity.MerkleOrdered34

set_option pp.all true in
#check @ShielddSecurity.MerkleOrdered34.orderedStep
#print axioms ShielddSecurity.MerkleOrdered34.orderedStep
set_option pp.all true in
#check @ShielddSecurity.MerkleOrdered34.root
#print axioms ShielddSecurity.MerkleOrdered34.root
set_option pp.all true in
#check @ShielddSecurity.MerkleOrdered34.exists_bits
#print axioms ShielddSecurity.MerkleOrdered34.exists_bits
set_option pp.all true in
#check @ShielddSecurity.MerkleOrdered34.first_step
#print axioms ShielddSecurity.MerkleOrdered34.first_step
set_option pp.all true in
#check @ShielddSecurity.MerkleOrdered34.later_step
#print axioms ShielddSecurity.MerkleOrdered34.later_step
set_option pp.all true in
#check @ShielddSecurity.MerkleOrdered34.meaning_eq
#print axioms ShielddSecurity.MerkleOrdered34.meaning_eq
set_option pp.all true in
#check @ShielddSecurity.MerkleOrdered34.arbitrary
#print axioms ShielddSecurity.MerkleOrdered34.arbitrary
set_option pp.all true in
#check @ShielddSecurity.MerkleOrdered34.anchor_sound
#print axioms ShielddSecurity.MerkleOrdered34.anchor_sound
set_option pp.all true in
#check @ShielddSecurity.MerkleOrdered34.total
#print axioms ShielddSecurity.MerkleOrdered34.total
