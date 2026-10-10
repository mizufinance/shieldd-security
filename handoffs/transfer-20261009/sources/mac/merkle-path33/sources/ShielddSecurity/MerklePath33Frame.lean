import ShielddSecurity.MerklePath33
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerklePath33Frame
open Compiler CompilerCompletion CompilerSegmentCompletion11
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F] [CharP F p]
def priorRows := (MerkleHash27Whole.priorRows++MerkleHash27Whole.selectedRows)++MerkleBits29.actualRows
include F in
theorem prior_support (row : Row) (member : row∈priorRows) (term : Nat×Int) (present : term∈row.a++row.b) : term.1<25884 ∨ term.1=copy := by
  rcases List.mem_append.mp member with member|member
  · rcases List.mem_append.mp member with member|member
    · rcases List.mem_append.mp member with member|member
      · rcases List.mem_append.mp member with member|member
        · rcases List.mem_append.mp member with member|member
          · have bound := CapturedPriorRows16Frame01.columns_below row member term present
            exact Or.inl (by omega)
          · rcases List.mem_append.mp member with member|member
            · rcases (TransferPoseidonThreeCallJoin15Frame01.whole_segment (F:=F)).support row member term present with below|equal
              · exact Or.inl (by change term.1<25044 at below;omega)
              · exact Or.inr equal
            · have checked : CapturedInitial73419Generic01.supportCheck 25044 [TransferPoseidonWidth3Call08Shared01.rawCopy]=true := by decide +kernel
              have bound := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
              rcases bound with below|equal
              · exact Or.inl (by omega)
              · exact Or.inr equal
        · have found := (RegistryWhole23.membership row).mpr member
          rcases (RegistryWhole23.segment (F:=F)).support row found term present with below|equal
          · exact Or.inl (by change term.1<25460 at below;omega)
          · exact Or.inr equal
      · rcases (MerkleSelection26Proof.segment (F:=F)).support row member term present with below|equal
        · exact Or.inl (by change term.1<25472 at below;omega)
        · exact Or.inr equal
    · exact (MerkleHash27Whole.segment (F:=F)).support row ((MerkleHash27Whole.membership row).mpr member) term present
  · have bound := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp MerkleBits29.support_checked row member) term present)
    exact Or.inl (by omega)
theorem preserved (base : Nat → F) (sat : Satisfies base priorRows) : Satisfies (MerklePath33.completed base) priorRows := by
  apply CompilerSegmentCompletion11.prior_preserved copy (MerklePath33.segment (F:=F)) base priorRows sat
  intro row member term present
  rcases prior_support (F:=F) row member term present with below|equal
  · exact Or.inl below
  · exact Or.inr (by change 32244≤term.1;change term.1=200692 at equal;omega)
def final (base : Nat → F) (n : Nat) := MerklePath33.completed (MerkleHash27Whole.final (MerkleBits29.seed base n))
theorem final_rows (base : Nat → F) (n : Nat) (bound : n<2^32) (meaning : base 135=(n:F))
    (one : base 0=1) (linked : base copy=base 0) :
    Satisfies (final base n) priorRows ∧ Satisfies (final base n) (MerklePath33.rows (F:=F)) := by
  have first := MerkleBits29.total base n bound meaning one linked
  have old : Satisfies (MerkleHash27Whole.final (MerkleBits29.seed base n)) priorRows := by
    intro row member
    rcases List.mem_append.mp member with member|member
    · rcases List.mem_append.mp member with member|member
      · exact first.1 row member
      · exact first.2.1 row member
    · exact first.2.2.1 row member
  refine ⟨preserved _ old,?_⟩
  apply MerklePath33.complete
  rw [MerkleHash27Whole.final_outside _ copy (Or.inr (by decide)),MerkleHash27Whole.final_outside _ 0 (Or.inl (by decide)),
    MerkleBits29.seed_outside base n copy (Or.inr (by decide)),MerkleBits29.seed_outside base n 0 (Or.inl (by decide))]
  exact linked
theorem final_outside (base : Nat → F) (n column : Nat)
    (bound : (column<22738 ∧ (column<184 ∨ 216≤column)) ∨ 32244≤column) : final base n column=base column := by
  unfold final
  rw [MerklePath33.outside _ column (by omega),MerkleHash27Whole.final_outside _ column (by omega),MerkleBits29.seed_outside base n column (by omega)]
end ShielddSecurity.MerklePath33Frame

set_option pp.all true in
#check @ShielddSecurity.MerklePath33Frame.priorRows
#print axioms ShielddSecurity.MerklePath33Frame.priorRows
set_option pp.all true in
#check @ShielddSecurity.MerklePath33Frame.prior_support
#print axioms ShielddSecurity.MerklePath33Frame.prior_support
set_option pp.all true in
#check @ShielddSecurity.MerklePath33Frame.preserved
#print axioms ShielddSecurity.MerklePath33Frame.preserved
set_option pp.all true in
#check @ShielddSecurity.MerklePath33Frame.final
#print axioms ShielddSecurity.MerklePath33Frame.final
set_option pp.all true in
#check @ShielddSecurity.MerklePath33Frame.final_rows
#print axioms ShielddSecurity.MerklePath33Frame.final_rows
set_option pp.all true in
#check @ShielddSecurity.MerklePath33Frame.final_outside
#print axioms ShielddSecurity.MerklePath33Frame.final_outside
