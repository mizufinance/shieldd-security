import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0063
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(16128,16329),(16129,16330),(16130,16331),(16131,16332),(16132,16333),(16133,16334),(16134,16335),(16135,16336),(16136,16337),(16137,16338),(16138,16339),(16139,16340),(16140,16341),(16141,16342),(16142,16343),(16143,16344),(16144,16345),(16145,16346),(16146,16347),(16147,16348),(16148,16349),(16149,16350),(16150,16351),(16151,16352),(16152,16353),(16153,16354),(16154,16355),(16155,16356),(16156,16357),(16157,16358),(16158,16359),(16159,16360),(16160,16361),(16161,16362),(16162,16363),(16163,16364),(16164,16365),(16165,16366),(16166,16367),(16167,16368),(16168,16369),(16169,16370),(16170,16371),(16171,16372),(16172,16373),(16173,16374),(16174,16375),(16175,16376),(16176,16377),(16177,16378),(16178,16379),(16179,16380),(16180,16381),(16181,16382),(16182,16383),(16183,16384),(16184,16385),(16185,16386),(16186,16387),(16187,16388),(16188,16389),(16189,16390),(16190,16391),(16191,16392),(16192,16393),(16193,16394),(16194,16395),(16195,16396),(16196,16397),(16197,16398),(16198,16399),(16199,16400),(16200,16401),(16201,16402),(16202,16403),(16203,16404),(16204,16405)]
theorem count : slots.length=77 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0063

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0063.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0063.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0063.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0063.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0063.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0063.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0063.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0063.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0063.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0063.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0063.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0063.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0063.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0063.sound
