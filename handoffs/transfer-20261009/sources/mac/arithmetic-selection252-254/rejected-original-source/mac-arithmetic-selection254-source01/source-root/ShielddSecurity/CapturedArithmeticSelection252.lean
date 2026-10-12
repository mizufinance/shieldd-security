import ShielddSecurity.CompilerSelectedTruth254
import ShielddSecurity.CapturedFullRelation58
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedArithmeticSelection252
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def Supported (index : Nat) : Prop := index<177954 ∨ index=200769
variable {F : Type} [Field F] [CharP F p]
theorem row_selected := @CompilerSelectedTruth254.row_selected
theorem selected_sound := @CompilerSelectedTruth254.selected_sound
theorem copy_position : CapturedFullRelation58.rowAt 200769=some (CompilerVerifierLinks53.linkRow 0 copy) :=
 (CapturedFullRelation58.assertion_position 22815 (by decide)).trans CapturedAssertionLinks57.copy_row
theorem supported_row (rho : Nat → F)
 (arithmetic : CompilerArithmeticBlock44.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
 (linked : rho copy=rho 0) (index : Nat) (support : Supported index) (row : Row)
 (found : CapturedFullRelation58.rowAt index=some row) : Square (eval rho row.a) (eval rho row.b) := by
 rcases support with bound|equal
 · rw [CapturedFullRelation58.arithmetic_position index bound] at found
   exact arithmetic index bound row found
 · subst index
   have same:CompilerVerifierLinks53.linkRow 0 copy=row := Option.some.inj (copy_position.symm.trans found)
   subst row
   exact (CompilerVerifierLinks53.link_iff rho 0 copy).mpr linked.symm
theorem of_arithmetic (indices : List Nat) (targets : List Row)
 (checked : CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices targets=true)
 (supports : ∀ index∈indices,Supported index) (rho : Nat → F)
 (arithmetic : CompilerArithmeticBlock44.SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
 (linked : rho copy=rho 0) : Satisfies rho targets :=
 CompilerSelectedTruth254.selected_sound (p:=p) (copy:=copy) _ _ indices targets checked rho linked
   (fun index member row found => supported_row rho arithmetic linked index (supports index member) row found)
theorem candidate_rows (base : Nat → F) (indices : List Nat) (targets : List Row)
 (checked : CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices targets=true)
 (supports : ∀ index∈indices,Supported index) :
 Satisfies (CapturedFullRelation58.candidate base) targets :=
 of_arithmetic indices targets checked supports _ (CapturedFullRelation58.candidate_arithmetic base)
   (CapturedFullRelation58.candidate_links base).2.2
omit [CharP F p] in
theorem range_supported (start count : Nat) (bound : start+count≤177954) :
 ∀ index∈List.range' start count,Supported index := by
 intro index member
 obtain ⟨offset,before,equal⟩:=List.mem_range'.mp member
 simp only [Nat.one_mul] at equal
 left
 omega
omit [CharP F p] in
theorem copies_supported (count : Nat) : ∀ index∈List.replicate count 200769,Supported index := by
 intro index member
 right
 exact (List.mem_replicate.mp member).2
end ShielddSecurity.CapturedArithmeticSelection252

set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticSelection252.Supported
#print axioms ShielddSecurity.CapturedArithmeticSelection252.Supported
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticSelection252.row_selected
#print axioms ShielddSecurity.CapturedArithmeticSelection252.row_selected
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticSelection252.selected_sound
#print axioms ShielddSecurity.CapturedArithmeticSelection252.selected_sound
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticSelection252.copy_position
#print axioms ShielddSecurity.CapturedArithmeticSelection252.copy_position
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticSelection252.supported_row
#print axioms ShielddSecurity.CapturedArithmeticSelection252.supported_row
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticSelection252.of_arithmetic
#print axioms ShielddSecurity.CapturedArithmeticSelection252.of_arithmetic
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticSelection252.candidate_rows
#print axioms ShielddSecurity.CapturedArithmeticSelection252.candidate_rows
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticSelection252.range_supported
#print axioms ShielddSecurity.CapturedArithmeticSelection252.range_supported
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmeticSelection252.copies_supported
#print axioms ShielddSecurity.CapturedArithmeticSelection252.copies_supported
