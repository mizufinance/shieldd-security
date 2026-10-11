import ShielddSecurity.CapturedFullRelation58
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BooleanHints207
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
-- This syntactic equality uses only decidable finite LC equality, never field evaluation.
def recipeEqual : Recipe → Recipe → Bool
 | .linear a b,.linear c d | .square a b,.square c d => decide (a=c ∧ b=d)
 | _,_ => false
theorem recipeEqual_iff (left right : Recipe) : recipeEqual left right=true ↔ left=right := by
 cases left <;> cases right <;> simp [recipeEqual]
def wireRecipe (column : Nat) : Recipe := .square [(column,1)] [(column,1)]
def checkSlot (recipes : Nat → Option (Bool × Recipe)) (slot : Nat × Nat) : Bool :=
 match recipes slot.1 with
 | some hint => recipeEqual hint.2 (wireRecipe slot.2)
 | none => false
def checkSlots (recipes : Nat → Option (Bool × Recipe)) (slots : List (Nat × Nat)) : Bool :=
 slots.all (checkSlot recipes)
theorem checkSlots_append (recipes : Nat → Option (Bool × Recipe)) (left right : List (Nat × Nat)) :
 checkSlots recipes (left++right)=(checkSlots recipes left && checkSlots recipes right) := by
 simp only [checkSlots,List.all_append]
theorem checked_slot (recipes : Nat → Option (Bool × Recipe)) (slots : List (Nat × Nat))
 (checked : checkSlots recipes slots=true) (slot : Nat × Nat) (member : slot∈slots) :
 ∃ outlined,recipes slot.1=some (outlined,wireRecipe slot.2) := by
 have valid:=List.all_eq_true.mp checked slot member
 cases found:recipes slot.1 with
 | none => simp only [checkSlot,found,Bool.false_eq_true] at valid
 | some hint =>
   have equal : hint.2=wireRecipe slot.2 :=
     (recipeEqual_iff _ _).mp (by simpa only [checkSlot,found] using valid)
   exact ⟨hint.1,by rw [←equal];exact found⟩
variable {F : Type} [Field F]
def bitValue (bit : Bool) : F := if bit then 1 else 0
def seeded (base : Nat → F) (bits : Nat → Bool) (columns : List Nat) : Nat → F :=
 fun column => if column∈columns then bitValue (bits column) else base column
theorem seeded_selected (base : Nat → F) (bits : Nat → Bool) (columns : List Nat)
 (column : Nat) (member : column∈columns) : seeded base bits columns column=bitValue (bits column) :=
 if_pos member
theorem seeded_outside (base : Nat → F) (bits : Nat → Bool) (columns : List Nat)
 (column : Nat) (outside : column∉columns) : seeded base bits columns column=base column :=
 if_neg outside
theorem wire_truth (rho : Nat → F) (column : Nat) :
 Truth rho (wireRecipe column) ↔ rho column=0 ∨ rho column=1 := by
 have reduced : Truth rho (wireRecipe column) ↔ rho column*rho column=rho column := by
   simp [Truth,wireRecipe,sourceLeft,sourceRight,expressionValue,eval]
 rw [reduced]
 constructor
 · intro square
   have product : rho column*(rho column-1)=0 := by rw [mul_sub,mul_one,square,sub_self]
   rcases mul_eq_zero.mp product with zero | one
   · exact Or.inl zero
   · exact Or.inr (sub_eq_zero.mp one)
 · rintro (zero | one)
   · rw [zero,mul_zero]
   · rw [one,mul_one]
theorem seeded_truth (base : Nat → F) (bits : Nat → Bool) (columns : List Nat)
 (recipes : Nat → Option (Bool × Recipe)) (slots : List (Nat × Nat))
 (checked : checkSlots recipes slots=true) (coverage : ∀ slot∈slots,slot.2∈columns)
 (slot : Nat × Nat) (member : slot∈slots)
 (hint : Bool × Recipe) (found : recipes slot.1=some hint) :
 Truth (seeded base bits columns) hint.2 := by
 obtain ⟨outlined,matching⟩:=checked_slot recipes slots checked slot member
 have same : hint=(outlined,wireRecipe slot.2) := Option.some.inj (found.symm.trans matching)
 rw [same]
 apply (wire_truth _ _).mpr
 rw [seeded_selected base bits columns slot.2 (coverage slot member)]
 cases bits slot.2 <;> simp [bitValue]
variable [CharP F p]
theorem candidate_truth (base : Nat → F) (bits : Nat → Bool) (columns : List Nat)
 (slots : List (Nat × Nat)) (checked : checkSlots CapturedFullAssertions54.recipeAt slots=true)
 (originals : ∀ slot∈slots,3≤slot.2 ∧ slot.2<22738)
 (coverage : ∀ slot∈slots,slot.2∈columns)
 (slot : Nat × Nat) (member : slot∈slots) (hint : Bool × Recipe)
 (found : CapturedFullAssertions54.recipeAt slot.1=some hint) :
 Truth (CapturedFullRelation58.candidate (seeded base bits columns)) hint.2 := by
 obtain ⟨outlined,matching⟩:=checked_slot _ slots checked slot member
 have same : hint=(outlined,wireRecipe slot.2) := Option.some.inj (found.symm.trans matching)
 rw [same]
 apply (wire_truth _ _).mpr
 have bound:=originals slot member
 have original:=CapturedFullRelation58.candidate_inputs
   (seeded base bits columns) (slot.2-3) (by omega)
 have index : 3+(slot.2-3)=slot.2 := by omega
 rw [index] at original
 rw [original,seeded_selected base bits columns slot.2 (coverage slot member)]
 cases bits slot.2 <;> simp [bitValue]
theorem candidate_selected (base : Nat → F) (bits : Nat → Bool) (columns : List Nat)
 (slots : List (Nat × Nat)) (checked : checkSlots CapturedFullAssertions54.recipeAt slots=true)
 (originals : ∀ slot∈slots,3≤slot.2 ∧ slot.2<22738)
 (coverage : ∀ slot∈slots,slot.2∈columns)
 (positions : ∀ slot∈slots,slot.1<22816) (slot : Nat × Nat) (member : slot∈slots) :
 ∃ row,CapturedFullRelation58.rowAt (177954+slot.1)=some row ∧
 Square (eval (CapturedFullRelation58.candidate (seeded base bits columns)) row.a)
        (eval (CapturedFullRelation58.candidate (seeded base bits columns)) row.b) := by
 obtain ⟨row,hint,foundRow,foundHint,valid⟩:=CapturedFullAssertions54.block.exact_checked slot.1 (positions slot member)
 have truth:=candidate_truth base bits columns slots checked originals coverage slot member hint foundHint
 have linked:=(CapturedFullRelation58.candidate_links (seeded base bits columns)).2.2
 exact ⟨row,by rw [CapturedFullRelation58.assertion_position slot.1 (positions slot member)];exact foundRow,
   (checked_iff copy row hint valid _ linked).mpr truth⟩
end ShielddSecurity.BooleanHints207

set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.recipeEqual
#print axioms ShielddSecurity.BooleanHints207.recipeEqual
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.recipeEqual_iff
#print axioms ShielddSecurity.BooleanHints207.recipeEqual_iff
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.wireRecipe
#print axioms ShielddSecurity.BooleanHints207.wireRecipe
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.checkSlot
#print axioms ShielddSecurity.BooleanHints207.checkSlot
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.checkSlots
#print axioms ShielddSecurity.BooleanHints207.checkSlots
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.checkSlots_append
#print axioms ShielddSecurity.BooleanHints207.checkSlots_append
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.checked_slot
#print axioms ShielddSecurity.BooleanHints207.checked_slot
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.bitValue
#print axioms ShielddSecurity.BooleanHints207.bitValue
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.seeded
#print axioms ShielddSecurity.BooleanHints207.seeded
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.seeded_selected
#print axioms ShielddSecurity.BooleanHints207.seeded_selected
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.seeded_outside
#print axioms ShielddSecurity.BooleanHints207.seeded_outside
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.wire_truth
#print axioms ShielddSecurity.BooleanHints207.wire_truth
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.seeded_truth
#print axioms ShielddSecurity.BooleanHints207.seeded_truth
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.candidate_truth
#print axioms ShielddSecurity.BooleanHints207.candidate_truth
set_option pp.all true in
#check @ShielddSecurity.BooleanHints207.candidate_selected
#print axioms ShielddSecurity.BooleanHints207.candidate_selected
