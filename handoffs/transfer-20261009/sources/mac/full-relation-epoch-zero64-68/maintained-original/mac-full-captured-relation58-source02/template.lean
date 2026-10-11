import ShielddSecurity.CapturedFullArithmetic52
import ShielddSecurity.CapturedAssertionLinks57
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedFullRelation58
open CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def rowAt (index : Nat) : Option Row :=
  if index<177954 then CapturedFullArithmetic52.rowAt index
  else if index<200770 then CapturedFullAssertions54.rowAt (index-177954) else none
theorem arithmetic_position (index : Nat) (bound : index<177954) :
    rowAt index=CapturedFullArithmetic52.rowAt index := by
  simp only [rowAt,bound,if_true]
theorem assertion_position (index : Nat) (bound : index<22816) :
    rowAt (177954+index)=CapturedFullAssertions54.rowAt index := by
  have notBefore : ¬177954+index<177954 := by omega
  have beforeEnd : 177954+index<200770 := by omega
  simp only [rowAt,notBefore,beforeEnd,if_false,if_true,Nat.add_sub_cancel_left]
theorem after_end (index : Nat) (bound : 200770≤index) : rowAt index=none := by
  have a : ¬index<177954 := by omega
  have b : ¬index<200770 := by omega
  simp only [rowAt,a,b,if_false]
theorem every_position (index : Nat) (bound : index<200770) : ∃ row,rowAt index=some row := by
  by_cases before : index<177954
  · rw [arithmetic_position index before]
    exact CapturedFullArithmetic52.every_position index before
  · have localBound : index-177954<22816 := by omega
    have same : index=177954+(index-177954) := by omega
    rw [same,assertion_position (index-177954) localBound]
    exact CapturedFullAssertions54.every_position (index-177954) localBound
variable {F : Type} [Field F] [CharP F p]
omit [CharP F p] in
theorem satisfies_split (rho : Nat → F) : SatisfiesAt rho rowAt 200770 ↔
    CompilerArithmeticBlock44.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 ∧
    SatisfiesAt rho CapturedFullAssertions54.rowAt 22816 := by
  constructor
  · intro sat
    constructor
    · intro index bound row found
      apply sat index (by omega) row
      rw [arithmetic_position index bound]
      exact found
    · intro index bound row found
      apply sat (177954+index) (by omega) row
      rw [assertion_position index bound]
      exact found
  · rintro ⟨arithmetic,assertions⟩ index bound row found
    by_cases before : index<177954
    · rw [arithmetic_position index before] at found
      exact arithmetic index before row found
    · have localBound : index-177954<22816 := by omega
      have same : index=177954+(index-177954) := by omega
      rw [same,assertion_position (index-177954) localBound] at found
      exact assertions (index-177954) localBound row found
theorem satisfies_iff (rho : Nat → F) : SatisfiesAt rho rowAt 200770 ↔
    CompilerArithmeticBlock44.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954 ∧
    TruthAt rho CapturedFullAssertions54.recipeAt 22816 := by
  rw [satisfies_split rho,CapturedAssertionLinks57.satisfies_iff rho]
theorem verifier_links (rho : Nat → F) (sat : SatisfiesAt rho rowAt 200770) :
    rho 1=rho 22737 ∧ rho 2=rho 9 ∧ rho copy=rho 0 := by
  have assertions := ((satisfies_split rho).mp sat).2
  exact ⟨CapturedAssertionLinks57.public_of_satisfies rho assertions,
    CapturedAssertionLinks57.committed_of_satisfies rho assertions,
    CapturedAssertionLinks57.copy_of_satisfies rho assertions⟩
noncomputable def candidate (base : Nat → F) : Nat → F :=
  CapturedFullArithmetic52.completed (CompilerVerifierLinks53.seeded base)
theorem candidate_arithmetic (base : Nat → F) :
    CompilerArithmeticBlock44.SatisfiesAt (candidate base) CapturedFullArithmetic52.rowAt 177954 :=
  CapturedFullArithmetic52.complete (CompilerVerifierLinks53.seeded base)
omit [CharP F p] in
theorem candidate_inputs (base : Nat → F) (input : Nat) (bound : input<22735) :
    candidate base (3+input)=base (3+input) := by
  exact (CapturedFullArithmetic52.original_inputs (CompilerVerifierLinks53.seeded base) input bound).trans
    (CompilerVerifierLinks53.seeded_original_inputs base input bound)
omit [CharP F p] in
theorem candidate_outside (base : Nat → F) (column : Nat)
    (outside : column<22738 ∨ 200692≤column)
    (different : column≠copy ∧ column≠1 ∧ column≠2) : candidate base column=base column := by
  exact (CapturedFullArithmetic52.outside (CompilerVerifierLinks53.seeded base) column outside).trans
    (CompilerVerifierLinks53.seeded_outside base column different)
omit [CharP F p] in
theorem candidate_links (base : Nat → F) :
    candidate base 1=candidate base 22737 ∧ candidate base 2=candidate base 9 ∧
    candidate base copy=candidate base 0 := by
  have a:=CapturedFullArithmetic52.fixed (CompilerVerifierLinks53.seeded base)
  have original:=CapturedFullArithmetic52.original_inputs (CompilerVerifierLinks53.seeded base)
  exact ⟨a.2.1.trans ((CompilerVerifierLinks53.seeded_public base).trans
      (original 22734 (by decide)).symm),
    a.2.2.1.trans ((CompilerVerifierLinks53.seeded_committed base).trans
      (original 6 (by decide)).symm),
    a.2.2.2.trans ((CompilerVerifierLinks53.seeded_copy base).trans a.1.symm)⟩
theorem candidate_full_iff (base : Nat → F) : SatisfiesAt (candidate base) rowAt 200770 ↔
    TruthAt (candidate base) CapturedFullAssertions54.recipeAt 22816 := by
  rw [satisfies_iff]
  exact and_iff_right (candidate_arithmetic base)
end ShielddSecurity.CapturedFullRelation58
