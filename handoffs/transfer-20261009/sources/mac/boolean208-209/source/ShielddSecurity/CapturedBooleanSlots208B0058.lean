import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0058
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(14848,15053),(14849,15054),(14850,15055),(14851,15056),(14852,15057),(14853,15058),(14854,15059),(14855,15060),(14856,15061),(14857,15062),(14858,15063),(14859,15064),(14860,15065),(14861,15066),(14862,15067),(14863,15068),(14864,15069),(14865,15070),(14866,15071),(14867,15072),(14868,15073),(14869,15074),(14870,15075),(14871,15076),(14872,15077),(14873,15078),(14874,15079),(14875,15080),(14876,15081),(14877,15082),(14878,15083),(14879,15084),(14880,15085),(14881,15086),(14882,15087),(14883,15088),(14884,15089),(14885,15090),(14886,15091),(14887,15092),(14888,15093),(14889,15094),(14890,15095),(14891,15096),(14892,15097),(14893,15098),(14894,15099),(14895,15100),(14896,15101),(14897,15102),(14898,15103),(14899,15104),(14900,15105),(14901,15106),(14902,15107),(14903,15108),(14904,15109),(14905,15110),(14906,15111),(14907,15112),(14908,15113),(14909,15114),(14910,15115),(14911,15116),(14912,15117),(14913,15118),(14914,15119),(14915,15120),(14916,15121),(14917,15122),(14918,15123),(14919,15124),(14920,15125),(14921,15126),(14922,15127),(14923,15128),(14924,15129),(14925,15130),(14926,15131),(14927,15132),(14928,15133),(14929,15134),(14930,15135),(14931,15136),(14932,15137),(14933,15138),(14934,15139),(14935,15140),(14936,15141),(14937,15142),(14938,15143)]
theorem count : slots.length=91 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0058

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0058.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0058.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0058.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0058.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0058.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0058.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0058.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0058.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0058.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0058.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0058.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0058.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0058.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0058.sound
