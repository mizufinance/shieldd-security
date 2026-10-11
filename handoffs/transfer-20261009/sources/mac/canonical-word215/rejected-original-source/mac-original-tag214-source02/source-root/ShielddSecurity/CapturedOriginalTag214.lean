import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedOriginalTag214
open CompilerAssertionBlock51 CompilerArithmeticTransport41
def recipe : Recipe := .square [(0,-1),(7607,1)] [(0,-1),(7607,1)]
theorem checked : CapturedFullAssertions54.recipeAt 7475=some (true,recipe) := rfl
variable {F : Type} [Field F]
theorem shifted_square (x zero : F) : Square (x-zero) (x-zero) ↔ x=zero ∨ x=zero+1 := by
 change (x-zero)*(x-zero)=x-zero ↔ _
 constructor
 · intro square
   have product : (x-zero)*((x-zero)-1)=0 := by rw [mul_sub,mul_one,square,sub_self]
   rcases mul_eq_zero.mp product with a | b
   · exact Or.inl (sub_eq_zero.mp a)
   · exact Or.inr (by linear_combination b)
 · rintro (rfl | rfl) <;> ring
theorem truth_iff (rho : Nat → F) : Truth rho recipe ↔ rho 7607=rho 0 ∨ rho 7607=rho 0+1 := by
 have expression : eval rho [(0,-1),(7607,1)]=rho 7607-rho 0 := by
   simp only [eval,Int.cast_neg,Int.cast_one,mul_neg_one,mul_one,add_zero]
   ring
 change Square (eval rho [(0,-1),(7607,1)]) (eval rho [(0,-1),(7607,1)]) ↔ _
 rw [expression]
 exact shifted_square _ _
noncomputable def seeded (base : Nat → F) (flag : Bool) : Nat → F :=
 fun column => if column=7607 then base 0+BooleanHints207.bitValue flag else base column
theorem seeded_outside (base : Nat → F) (flag : Bool) (column : Nat) (different : column≠7607) :
 seeded base flag column=base column := if_neg different
theorem seeded_value (base : Nat → F) (flag : Bool) :
 seeded base flag 7607=base 0+BooleanHints207.bitValue flag := if_pos rfl
theorem seeded_truth (base : Nat → F) (flag : Bool) : Truth (seeded base flag) recipe := by
 apply (truth_iff _).mpr
 rw [seeded_value,seeded_outside base flag 0 (by decide)]
 cases flag <;> simp [BooleanHints207.bitValue]
theorem candidate_truth (base : Nat → F) (flag : Bool) :
 Truth (CapturedFullRelation58.candidate (seeded base flag)) recipe := by
 apply (truth_iff _).mpr
 have original:=CapturedFullRelation58.candidate_inputs (seeded base flag) 7604 (by decide)
 have zero:=CapturedFullRelation58.candidate_outside (seeded base flag) 0 (by decide) (by decide)
 change CapturedFullRelation58.candidate (seeded base flag) 7607=seeded base flag 7607 at original
 rw [original,zero]
 exact (truth_iff _).mp (seeded_truth base flag)
variable [CharP F p]
theorem selected (base : Nat → F) (flag : Bool) :
 ∃ row,CapturedFullRelation58.rowAt 185429=some row ∧
 Square (eval (CapturedFullRelation58.candidate (seeded base flag)) row.a)
        (eval (CapturedFullRelation58.candidate (seeded base flag)) row.b) := by
 obtain ⟨row,hint,found,specified,check⟩:=CapturedFullAssertions54.block.exact_checked 7475 (by decide)
 have equal : hint=(true,recipe) := Option.some.inj (specified.symm.trans checked)
 have truth : Truth (CapturedFullRelation58.candidate (seeded base flag)) hint.2 := by
   rw [equal]
   exact candidate_truth base flag
 refine ⟨row,?_,(CompilerAssertionBlock51.checked_iff copy row hint check _
   (CapturedFullRelation58.candidate_links (seeded base flag)).2.2).mpr truth⟩
 rw [CapturedFullRelation58.assertion_position 7475 (by decide)]
 exact found
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 rho 7607=rho 0 ∨ rho 7607=rho 0+1 :=
 (truth_iff rho).mp (((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2 7475 (by decide) _ checked)
theorem tag_sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (zero : rho 0=1) : rho 7607=1 ∨ rho 7607=2 := by
 have tag:=sound rho satisfied
 simpa only [zero,one_add_one_eq_two] using tag
end ShielddSecurity.CapturedOriginalTag214

set_option pp.all true in
#check @ShielddSecurity.CapturedOriginalTag214.recipe
#print axioms ShielddSecurity.CapturedOriginalTag214.recipe
set_option pp.all true in
#check @ShielddSecurity.CapturedOriginalTag214.checked
#print axioms ShielddSecurity.CapturedOriginalTag214.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedOriginalTag214.shifted_square
#print axioms ShielddSecurity.CapturedOriginalTag214.shifted_square
set_option pp.all true in
#check @ShielddSecurity.CapturedOriginalTag214.truth_iff
#print axioms ShielddSecurity.CapturedOriginalTag214.truth_iff
set_option pp.all true in
#check @ShielddSecurity.CapturedOriginalTag214.seeded
#print axioms ShielddSecurity.CapturedOriginalTag214.seeded
set_option pp.all true in
#check @ShielddSecurity.CapturedOriginalTag214.seeded_outside
#print axioms ShielddSecurity.CapturedOriginalTag214.seeded_outside
set_option pp.all true in
#check @ShielddSecurity.CapturedOriginalTag214.seeded_value
#print axioms ShielddSecurity.CapturedOriginalTag214.seeded_value
set_option pp.all true in
#check @ShielddSecurity.CapturedOriginalTag214.seeded_truth
#print axioms ShielddSecurity.CapturedOriginalTag214.seeded_truth
set_option pp.all true in
#check @ShielddSecurity.CapturedOriginalTag214.candidate_truth
#print axioms ShielddSecurity.CapturedOriginalTag214.candidate_truth
set_option pp.all true in
#check @ShielddSecurity.CapturedOriginalTag214.selected
#print axioms ShielddSecurity.CapturedOriginalTag214.selected
set_option pp.all true in
#check @ShielddSecurity.CapturedOriginalTag214.sound
#print axioms ShielddSecurity.CapturedOriginalTag214.sound
set_option pp.all true in
#check @ShielddSecurity.CapturedOriginalTag214.tag_sound
#print axioms ShielddSecurity.CapturedOriginalTag214.tag_sound
