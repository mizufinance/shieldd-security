import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0044
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(11399,11612),(11400,11613),(11401,11614),(11402,11615),(11403,11616),(11404,11617),(11405,11618),(11406,11619),(11407,11620),(11408,11621),(11409,11622),(11410,11623),(11411,11624),(11412,11625),(11413,11626),(11414,11627),(11415,11628),(11416,11629),(11417,11630),(11418,11631),(11419,11632),(11420,11633),(11421,11634),(11422,11635),(11423,11636),(11424,11637),(11425,11638),(11426,11639),(11427,11640),(11428,11641),(11429,11642),(11430,11643),(11431,11644),(11432,11645),(11433,11646),(11434,11647),(11435,11648),(11436,11649),(11437,11650),(11438,11651),(11439,11652),(11440,11653),(11441,11654),(11442,11655),(11443,11656),(11444,11657),(11445,11658),(11446,11659),(11447,11660),(11448,11661),(11449,11662),(11450,11663),(11451,11664),(11452,11665),(11453,11666),(11454,11667),(11455,11668),(11456,11669),(11457,11670),(11458,11671),(11459,11672),(11460,11673),(11461,11674),(11462,11675),(11463,11676),(11464,11677),(11465,11678),(11466,11679),(11467,11680),(11468,11681),(11469,11682),(11470,11683),(11471,11684),(11472,11685),(11473,11686),(11474,11687),(11475,11688),(11476,11689),(11477,11690),(11478,11691),(11479,11692),(11480,11693),(11481,11694),(11482,11695),(11483,11696),(11484,11697),(11485,11698),(11486,11699),(11487,11700),(11488,11701),(11489,11702),(11490,11703),(11491,11704),(11492,11705),(11493,11706),(11494,11707),(11495,11708),(11496,11709),(11497,11710),(11498,11711),(11499,11712),(11500,11713),(11501,11714),(11502,11715),(11503,11716),(11504,11717),(11505,11718),(11506,11719),(11507,11720),(11508,11721),(11509,11722),(11510,11723),(11511,11724),(11512,11725),(11513,11726),(11514,11727),(11515,11728),(11516,11729),(11517,11730),(11518,11731),(11519,11732)]
theorem count : slots.length=121 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0044

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0044.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0044.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0044.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0044.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0044.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0044.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0044.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0044.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0044.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0044.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0044.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0044.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0044.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0044.sound
