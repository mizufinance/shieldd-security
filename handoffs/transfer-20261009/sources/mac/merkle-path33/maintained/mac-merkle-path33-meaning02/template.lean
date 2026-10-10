import ShielddSecurity.MerklePath33Frame
import ShielddSecurity.MerklePath33AnchorData
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerklePath33Meaning
open Compiler Poseidon
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
omit [CharP F p] in
def walk (rho : Nat → F) (initial : F) : Nat → F
  | 0 => initial
  | n+1 => MerkleFamily32Whole.next ⟨n%15,Nat.mod_lt n (by decide)⟩ rho (walk rho initial n)
omit [CharP F p] in
def meaning (rho : Nat → F) (n : Nat) := walk rho (MerkleInputMeaning28.pathMeaning rho) n
theorem initial_eq (rho : Nat → F) (one : rho 0=1)
    (prior : Satisfies rho MerkleHash27Whole.priorRows) (first : Satisfies rho MerkleHash27Whole.selectedRows)
    (n : Nat) : MerklePath33.path rho n=meaning rho n := by
  induction n with
  | zero => exact MerkleInputMeaning28.arbitrary rho one prior first
  | succ n ih => change MerkleFamily32Whole.next _ rho (MerklePath33.path rho n)=MerkleFamily32Whole.next _ rho (meaning rho n);rw [ih]
theorem arbitrary (rho : Nat → F) (one : rho 0=1)
    (prior : Satisfies rho MerkleHash27Whole.priorRows) (first : Satisfies rho MerkleHash27Whole.selectedRows)
    (rest : Satisfies rho (MerklePath33.rows (F:=F))) :
    eval rho MerklePath33AnchorData.output=meaning rho 15 := by
  have value := MerklePath33.arbitrary_path rho one rest 15 (by decide)
  rw [initial_eq rho one prior first] at value
  change eval rho (MerkleFamily32Tables.resultList[14]?.getD [])=meaning rho 15 at value
  rw [MerklePath33AnchorData.output_exact] at value
  exact value
omit [CharP F p] in
theorem next_agrees (i : Fin 15) (rho sigma : Nat → F) (node : F)
    (values : ∀ column<22738,rho column=sigma column) : MerkleFamily32Whole.next i rho node=MerkleFamily32Whole.next i sigma node := by
  have h := i.isLt
  unfold MerkleFamily32Whole.next
  rw [values _ (by omega),values _ (by omega),values _ (by omega),values _ (by omega),values _ (by omega)]
omit [CharP F p] in
theorem initial_agrees (rho sigma : Nat → F) (values : ∀ column<22738,rho column=sigma column) :
    MerkleInputMeaning28.pathMeaning rho=MerkleInputMeaning28.pathMeaning sigma := by
  simp only [MerkleInputMeaning28.pathMeaning,MerkleInputMeaning28.registryMeaning,RegistryInputJoin24.semanticInputs,
    values 11 (by decide),values 12 (by decide),values 13 (by decide),values 14 (by decide),values 15 (by decide),values 21 (by decide),values 22 (by decide),values 23 (by decide),values 24 (by decide),values 30 (by decide),values 31 (by decide),values 32 (by decide),values 33 (by decide),values 34 (by decide),values 35 (by decide),values 36 (by decide),values 42 (by decide),values 43 (by decide),values 184 (by decide),values 185 (by decide),values 136 (by decide),values 137 (by decide),values 138 (by decide)]
omit [CharP F p] in
theorem meaning_agrees (rho sigma : Nat → F) (values : ∀ column<22738,rho column=sigma column) (n : Nat) : meaning rho n=meaning sigma n := by
  induction n with
  | zero => exact initial_agrees rho sigma values
  | succ n ih =>
    change MerkleFamily32Whole.next _ rho (meaning rho n)=MerkleFamily32Whole.next _ sigma (meaning sigma n)
    rw [ih,next_agrees _ rho sigma _ values]
theorem total (base : Nat → F) (n : Nat) (bound : n<2^32) (position : base 135=(n:F))
    (one : base 0=1) (linked : base copy=base 0) :
    Satisfies (MerklePath33Frame.final base n) MerklePath33Frame.priorRows ∧
    Satisfies (MerklePath33Frame.final base n) (MerklePath33.rows (F:=F)) ∧
    eval (MerklePath33Frame.final base n) MerklePath33AnchorData.output=meaning (MerkleBits29.seed base n) 15 := by
  have done := MerklePath33Frame.final_rows base n bound position one linked
  have values (column : Nat) (below : column<22738) : MerklePath33Frame.final base n column=MerkleBits29.seed base n column := by
    unfold MerklePath33Frame.final
    rw [MerklePath33.outside _ column (Or.inl (by omega)),MerkleHash27Whole.final_outside _ column (Or.inl below)]
  have prior : Satisfies (MerklePath33Frame.final base n) MerkleHash27Whole.priorRows := fun row member => done.1 row (List.mem_append_left _ (List.mem_append_left _ member))
  have first : Satisfies (MerklePath33Frame.final base n) MerkleHash27Whole.selectedRows := fun row member => done.1 row (List.mem_append_left _ (List.mem_append_right _ member))
  have oneFinal : MerklePath33Frame.final base n 0=1 := (values 0 (by decide)).trans ((MerkleBits29.seed_outside base n 0 (Or.inl (by decide))).trans one)
  refine ⟨done.1,done.2,?_⟩
  rw [arbitrary _ oneFinal prior first done.2,meaning_agrees _ _ values]
theorem anchor_sound (rho : Nat → F) (one : rho 0=1)
    (prior : Satisfies rho MerkleHash27Whole.priorRows) (first : Satisfies rho MerkleHash27Whole.selectedRows)
    (rest : Satisfies rho (MerklePath33.rows (F:=F))) (anchor : Satisfies rho [MerklePath33AnchorData.anchor]) :
    rho 4=meaning rho 15 := by
  have same := checked_assertion_sound (p:=p) rho [MerklePath33AnchorData.anchor] MerklePath33AnchorData.output [(4,1)] anchor MerklePath33AnchorData.anchor_checked
  simpa only [eval,Int.cast_one,one_mul,add_zero] using same.symm.trans (arbitrary rho one prior first rest)
theorem anchor_complete (base : Nat → F) (n : Nat) (bound : n<2^32) (position : base 135=(n:F))
    (one : base 0=1) (linked : base copy=base 0)
    (legal_anchor : base 4=meaning (MerkleBits29.seed base n) 15) :
    Satisfies (MerklePath33Frame.final base n) [MerklePath33AnchorData.anchor] := by
  have value := (total base n bound position one linked).2.2
  have fixed : MerklePath33Frame.final base n 4=base 4 := MerklePath33Frame.final_outside base n 4 (Or.inl ⟨by decide,Or.inl (by decide)⟩)
  have equality : eval (MerklePath33Frame.final base n) MerklePath33AnchorData.output=eval (MerklePath33Frame.final base n) [(4,1)] := by simpa [eval,fixed,legal_anchor] using value
  have sat : Satisfies (MerklePath33Frame.final base n) [⟨subtract MerklePath33AnchorData.output [(4,1)],[]⟩] := by
    intro row member
    have same : row=⟨subtract MerklePath33AnchorData.output [(4,1)],[]⟩ := by simpa using member
    subst row
    change Square (eval (MerklePath33Frame.final base n) (subtract MerklePath33AnchorData.output [(4,1)])) 0
    rw [eval_subtract,equality,sub_self]
    rfl
  exact MerkleBits29.transfer _ [MerklePath33AnchorData.anchor] [⟨subtract MerklePath33AnchorData.output [(4,1)],[]⟩] MerklePath33AnchorData.reverse_checked sat
end ShielddSecurity.MerklePath33Meaning
