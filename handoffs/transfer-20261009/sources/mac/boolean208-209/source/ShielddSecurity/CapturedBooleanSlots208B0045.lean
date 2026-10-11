import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0045
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(11520,11733),(11521,11734),(11522,11735),(11523,11736),(11524,11737),(11525,11738),(11526,11739),(11527,11740),(11528,11741),(11529,11742),(11530,11743),(11531,11744),(11532,11745),(11533,11746),(11534,11747),(11535,11748),(11536,11749),(11537,11750),(11538,11751),(11539,11752),(11540,11753),(11541,11754),(11542,11755),(11543,11756),(11544,11757),(11545,11758),(11546,11759),(11547,11760),(11548,11761),(11549,11762),(11550,11763),(11551,11764),(11552,11765),(11553,11766),(11554,11767),(11555,11768),(11556,11769),(11557,11770),(11558,11771),(11559,11772),(11560,11773),(11561,11774),(11562,11775),(11563,11776),(11564,11777),(11565,11778),(11566,11779),(11567,11780),(11568,11781),(11569,11782),(11570,11783),(11571,11784),(11572,11785),(11573,11786),(11574,11787),(11575,11788),(11576,11789),(11577,11790),(11578,11791),(11579,11792),(11580,11793),(11581,11794),(11582,11795),(11583,11796),(11584,11797),(11585,11798),(11586,11799),(11587,11800),(11588,11801),(11589,11802),(11590,11803),(11591,11804),(11592,11805),(11593,11806),(11594,11807),(11595,11808),(11596,11809),(11597,11810),(11598,11811),(11599,11812),(11600,11813),(11601,11814),(11602,11815),(11603,11816),(11604,11817),(11605,11818),(11606,11819),(11607,11820),(11608,11821),(11609,11822),(11610,11823),(11611,11824),(11612,11825),(11613,11826),(11614,11827),(11615,11828),(11616,11829),(11617,11830),(11618,11831),(11619,11832),(11620,11833),(11621,11834),(11622,11835),(11623,11836),(11624,11837),(11625,11838),(11626,11839),(11627,11840),(11628,11841),(11629,11842),(11630,11843),(11631,11844),(11632,11845),(11633,11846),(11634,11847),(11635,11848),(11636,11849),(11637,11850),(11638,11851),(11639,11852),(11640,11853),(11641,11854),(11642,11855),(11643,11856),(11644,11857),(11645,11858),(11646,11859),(11647,11860),(11648,11861),(11649,11862),(11650,11863)]
theorem count : slots.length=131 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0045

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0045.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0045.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0045.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0045.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0045.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0045.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0045.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0045.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0045.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0045.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0045.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0045.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0045.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0045.sound
