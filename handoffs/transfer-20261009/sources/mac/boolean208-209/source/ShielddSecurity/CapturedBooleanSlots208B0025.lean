import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0025
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(6400,6547),(6401,6548),(6402,6549),(6403,6550),(6404,6551),(6405,6552),(6406,6553),(6407,6554),(6408,6555),(6409,6556),(6410,6557),(6411,6558),(6412,6559),(6413,6560),(6414,6561),(6415,6562),(6416,6563),(6417,6564),(6418,6565),(6419,6566),(6420,6567),(6421,6568),(6422,6569),(6423,6570),(6424,6571),(6425,6572),(6426,6573),(6427,6574),(6428,6575),(6429,6576),(6430,6577),(6431,6578),(6432,6579),(6433,6580),(6434,6581),(6435,6582),(6436,6583),(6437,6584),(6438,6585),(6439,6586)]
theorem count : slots.length=40 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0025

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0025.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0025.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0025.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0025.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0025.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0025.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0025.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0025.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0025.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0025.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0025.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0025.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0025.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0025.sound
