import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0023
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(6058,6196),(6059,6197),(6060,6198),(6061,6199),(6062,6200),(6063,6201),(6064,6202),(6065,6203),(6066,6204),(6067,6205),(6068,6206),(6069,6207),(6070,6208),(6071,6209),(6072,6210),(6073,6211),(6074,6212),(6075,6213),(6076,6214),(6077,6215),(6078,6216),(6079,6217),(6080,6218),(6081,6219),(6082,6220),(6083,6221),(6084,6222),(6085,6223),(6086,6224),(6087,6225),(6088,6226),(6089,6227),(6090,6228),(6091,6229),(6092,6230),(6093,6231),(6094,6232),(6095,6233),(6096,6234),(6097,6235),(6098,6236),(6099,6237),(6100,6238),(6101,6239),(6102,6240),(6103,6241),(6104,6242),(6105,6243),(6106,6244),(6107,6245),(6108,6246),(6109,6247),(6110,6248),(6111,6249),(6112,6250),(6113,6251),(6114,6252),(6115,6253),(6116,6254),(6117,6255),(6118,6256),(6119,6257),(6120,6258),(6121,6259),(6122,6260),(6123,6261),(6124,6262),(6125,6263),(6126,6264),(6127,6265),(6128,6266),(6129,6267),(6130,6268),(6131,6269),(6132,6270),(6133,6271),(6134,6272),(6135,6273),(6136,6274),(6137,6275),(6138,6276),(6139,6277),(6140,6278),(6141,6279),(6142,6280),(6143,6281)]
theorem count : slots.length=86 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0023

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0023.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0023.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0023.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0023.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0023.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0023.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0023.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0023.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0023.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0023.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0023.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0023.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0023.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0023.sound
