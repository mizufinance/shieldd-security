import ShielddSecurity.CapturedWordCompatibility251
import ShielddSecurity.CapturedWordRoot213
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.LegalWordNormalization272
open WordHints210
def Alias (column : Nat) : Prop := column=9059 ∨ column=10591 ∨ column=20935
instance aliasDecidable (column : Nat) : Decidable (Alias column) := inferInstanceAs (Decidable (column=9059 ∨ column=10591 ∨ column=20935))
def normalized (numbers : Nat → Nat) (column : Nat) : Nat :=
 if column=9059 then numbers 9061%2 else if column=10591 then numbers 10593%2
 else if column=20935 then numbers 20937%2 else numbers column
theorem fixed (numbers : Nat → Nat) (column : Nat) (outside : ¬Alias column) : normalized numbers column=numbers column := by
 have first : column≠9059 := fun equal => outside (Or.inl equal)
 have second : column≠10591 := fun equal => outside (Or.inr (Or.inl equal))
 have third : column≠20935 := fun equal => outside (Or.inr (Or.inr equal))
 simp only [normalized,if_neg first,if_neg second,if_neg third]
theorem parities (numbers : Nat → Nat) :
 normalized numbers 9059%2=normalized numbers 9061%2 ∧
 normalized numbers 10591%2=normalized numbers 10593%2 ∧
 normalized numbers 20935%2=normalized numbers 20937%2 := by
 simp [normalized,Nat.mod_mod]
theorem coherent (numbers : Nat → Nat) : SharedWordFlags220.Coherent
 (SharedWordFlags220.assignments SharedWordWitness221.wordSlots (normalized numbers)) :=
 CapturedWordCompatibility251.coherent (normalized numbers) (parities numbers).1
   (parities numbers).2.1 (parities numbers).2.2
theorem widths_checked : CapturedWordRoot213.words.all
 (fun entry => decide (Alias entry.1.value → entry.1.width=1))=true := by decide +kernel
theorem alias_width (entry : Slot × Nat) (member : entry∈CapturedWordRoot213.words)
 (alias : Alias entry.1.value) : entry.1.width=1 :=
 (of_decide_eq_true ((List.all_eq_true.mp widths_checked) entry member)) alias
theorem alias_small (numbers : Nat → Nat) (column : Nat) (alias : Alias column) : normalized numbers column<2 := by
 rcases alias with first|second|third
 · subst column
   simpa [normalized] using Nat.mod_lt (numbers 9061) (by decide : 0<2)
 · subst column
   simpa [normalized] using Nat.mod_lt (numbers 10593) (by decide : 0<2)
 · subst column
   simpa [normalized] using Nat.mod_lt (numbers 20937) (by decide : 0<2)
theorem bounded (numbers : Nat → Nat)
 (other : ∀ entry∈CapturedWordRoot213.words,¬Alias entry.1.value → numbers entry.1.value<2^entry.1.width) :
 ∀ entry∈CapturedWordRoot213.words,normalized numbers entry.1.value<2^entry.1.width := by
 intro entry member
 by_cases alias : Alias entry.1.value
 · rw [alias_width entry member alias]
   exact alias_small numbers entry.1.value alias
 · rw [fixed numbers entry.1.value alias]
   exact other entry member alias
end ShielddSecurity.LegalWordNormalization272

set_option pp.all true in
#check @ShielddSecurity.LegalWordNormalization272.Alias
#print axioms ShielddSecurity.LegalWordNormalization272.Alias
set_option pp.all true in
#check @ShielddSecurity.LegalWordNormalization272.aliasDecidable
#print axioms ShielddSecurity.LegalWordNormalization272.aliasDecidable
set_option pp.all true in
#check @ShielddSecurity.LegalWordNormalization272.normalized
#print axioms ShielddSecurity.LegalWordNormalization272.normalized
set_option pp.all true in
#check @ShielddSecurity.LegalWordNormalization272.fixed
#print axioms ShielddSecurity.LegalWordNormalization272.fixed
set_option pp.all true in
#check @ShielddSecurity.LegalWordNormalization272.parities
#print axioms ShielddSecurity.LegalWordNormalization272.parities
set_option pp.all true in
#check @ShielddSecurity.LegalWordNormalization272.coherent
#print axioms ShielddSecurity.LegalWordNormalization272.coherent
set_option pp.all true in
#check @ShielddSecurity.LegalWordNormalization272.widths_checked
#print axioms ShielddSecurity.LegalWordNormalization272.widths_checked
set_option pp.all true in
#check @ShielddSecurity.LegalWordNormalization272.alias_width
#print axioms ShielddSecurity.LegalWordNormalization272.alias_width
set_option pp.all true in
#check @ShielddSecurity.LegalWordNormalization272.alias_small
#print axioms ShielddSecurity.LegalWordNormalization272.alias_small
set_option pp.all true in
#check @ShielddSecurity.LegalWordNormalization272.bounded
#print axioms ShielddSecurity.LegalWordNormalization272.bounded
