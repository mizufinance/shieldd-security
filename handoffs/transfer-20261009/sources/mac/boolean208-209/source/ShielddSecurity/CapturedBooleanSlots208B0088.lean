import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0088
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(22528,22456),(22529,22457),(22530,22458),(22531,22459),(22532,22460),(22533,22461),(22534,22462),(22535,22463),(22536,22464),(22537,22465),(22538,22466),(22539,22467),(22540,22468),(22541,22469),(22542,22470),(22543,22471),(22544,22472),(22545,22473),(22546,22474),(22547,22475),(22548,22476),(22549,22477),(22550,22478),(22551,22479),(22552,22480),(22553,22481),(22554,22482),(22555,22483)]
theorem count : slots.length=28 := rfl
theorem checked : checkSlots CapturedFullAssertions54.recipeAt slots=true := by decide
theorem originals : ∀ slot∈slots,3≤slot.2 ∧ slot.2<22738 := by decide
theorem positions : ∀ slot∈slots,slot.1<22816 := by decide
variable {F : Type} [Field F] [CharP F p]
theorem constructor (base : Nat → F) (bits : Nat → Bool) (columns : List Nat)
 (coverage : ∀ slot∈slots,slot.2∈columns) : ∀ slot∈slots,
 ∃ row,CapturedFullRelation58.rowAt (177954+slot.1)=some row ∧
 Square (eval (CapturedFullRelation58.candidate (seeded base bits columns)) row.a)
        (eval (CapturedFullRelation58.candidate (seeded base bits columns)) row.b) :=
 fun slot member => candidate_selected base bits columns slots checked originals coverage positions slot member
theorem sound (rho : Nat → F)
 (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 ∀ slot∈slots,rho slot.2=0 ∨ rho slot.2=1 := by
 intro slot member
 obtain ⟨outlined,matching⟩:=checked_slot _ slots checked slot member
 have truth:=((CapturedFullRelation58.satisfies_iff rho).mp satisfied).2 slot.1
   (positions slot member) (outlined,wireRecipe slot.2) matching
 exact (wire_truth rho slot.2).mp truth
end ShielddSecurity.CapturedBooleanSlots208B0088

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0088.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0088.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0088.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0088.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0088.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0088.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0088.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0088.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0088.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0088.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0088.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0088.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0088.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0088.sound
