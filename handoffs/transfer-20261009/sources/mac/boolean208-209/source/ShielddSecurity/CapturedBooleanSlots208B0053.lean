import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0053
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(13568,13777),(13569,13778),(13570,13779),(13571,13780),(13572,13781),(13573,13782),(13574,13783),(13575,13784),(13576,13785),(13577,13786),(13578,13787),(13579,13788),(13580,13789),(13581,13790),(13582,13791),(13583,13792),(13584,13793),(13585,13794),(13586,13795),(13587,13796),(13588,13797),(13589,13798),(13590,13799),(13591,13800),(13592,13801),(13593,13802),(13594,13803),(13595,13804),(13596,13805),(13597,13806),(13598,13807),(13599,13808),(13600,13809),(13601,13810),(13602,13811),(13603,13812),(13604,13813),(13605,13814),(13606,13815),(13607,13816),(13608,13817),(13609,13818),(13610,13819),(13611,13820),(13612,13821),(13613,13822),(13614,13823),(13615,13824),(13616,13825),(13617,13826),(13618,13827),(13619,13828),(13620,13829),(13621,13830),(13622,13831),(13623,13832),(13624,13833),(13625,13834),(13626,13835),(13627,13836),(13628,13837),(13629,13838),(13630,13839),(13631,13840),(13632,13841),(13633,13842),(13634,13843),(13635,13844),(13636,13845),(13637,13846),(13638,13847),(13639,13848),(13640,13849),(13641,13850),(13642,13851),(13643,13852),(13644,13853),(13645,13854),(13646,13855),(13647,13856),(13648,13857),(13649,13858),(13650,13859),(13651,13860),(13652,13861),(13653,13862),(13654,13863),(13655,13864),(13656,13865),(13657,13866),(13658,13867),(13659,13868),(13660,13869),(13661,13870),(13662,13871),(13663,13872),(13664,13873),(13665,13874),(13666,13875),(13667,13876),(13668,13877),(13669,13878),(13670,13879),(13671,13880),(13672,13881)]
theorem count : slots.length=105 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0053

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0053.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0053.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0053.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0053.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0053.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0053.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0053.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0053.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0053.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0053.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0053.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0053.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0053.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0053.sound
