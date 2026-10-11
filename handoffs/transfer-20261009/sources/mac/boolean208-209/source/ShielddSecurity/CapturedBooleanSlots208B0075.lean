import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0075
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(19200,19364),(19201,19365),(19202,19366),(19203,19367),(19204,19368),(19205,19369),(19206,19370),(19207,19371),(19208,19372),(19209,19373),(19210,19374),(19211,19375),(19212,19376),(19213,19377),(19214,19378),(19215,19379),(19216,19380),(19217,19381),(19218,19382),(19219,19383),(19220,19384),(19221,19385),(19222,19386),(19223,19387),(19224,19388),(19225,19389),(19226,19390),(19227,19391),(19228,19392),(19229,19393),(19230,19394),(19231,19395),(19232,19396),(19233,19397),(19234,19398),(19235,19399),(19236,19400),(19237,19401),(19238,19402),(19239,19403),(19240,19404),(19241,19405),(19242,19406),(19243,19407),(19244,19408),(19245,19409),(19246,19410),(19247,19411),(19248,19412),(19249,19413),(19250,19414),(19251,19415),(19252,19416),(19253,19417),(19254,19418),(19255,19419),(19256,19420),(19257,19421),(19258,19422),(19259,19423),(19260,19424),(19261,19425),(19262,19426),(19263,19427),(19264,19428),(19265,19429),(19266,19430),(19267,19431),(19268,19432),(19269,19433),(19270,19434),(19271,19435),(19272,19436),(19273,19437),(19274,19438),(19275,19439),(19276,19440),(19277,19441),(19278,19442),(19279,19443),(19280,19444),(19281,19445),(19282,19446),(19283,19447),(19284,19448),(19285,19449),(19286,19450),(19287,19451),(19288,19452),(19289,19453),(19290,19454),(19307,19457),(19310,19459),(19313,19461),(19316,19463),(19319,19465),(19322,19467),(19325,19469),(19328,19471),(19331,19473),(19334,19475),(19337,19477),(19340,19479),(19343,19481),(19346,19483),(19349,19485),(19352,19487),(19355,19489),(19358,19491),(19361,19493),(19364,19495),(19367,19497),(19370,19499),(19373,19501),(19376,19503),(19379,19505),(19382,19507),(19385,19509),(19388,19511),(19391,19513),(19394,19515),(19397,19517),(19400,19519),(19403,19521),(19407,19523),(19410,19525),(19413,19527),(19416,19529),(19419,19531),(19422,19533),(19425,19535),(19428,19537),(19431,19539),(19434,19541),(19437,19543),(19440,19545),(19443,19547),(19446,19549),(19449,19551),(19452,19553),(19455,19555)]
theorem count : slots.length=141 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0075

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0075.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0075.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0075.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0075.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0075.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0075.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0075.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0075.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0075.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0075.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0075.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0075.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0075.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0075.sound
