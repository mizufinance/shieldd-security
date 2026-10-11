import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0067
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(17227,17415),(17228,17416),(17229,17417),(17230,17418),(17231,17419),(17232,17420),(17233,17421),(17234,17422),(17235,17423),(17236,17424),(17237,17425),(17238,17426),(17239,17427),(17240,17428),(17241,17429),(17242,17430),(17243,17431),(17244,17432),(17245,17433),(17246,17434),(17247,17435),(17248,17436),(17249,17437),(17250,17438),(17251,17439),(17252,17440),(17253,17441),(17254,17442),(17255,17443),(17256,17444),(17257,17445),(17258,17446),(17259,17447),(17260,17448),(17261,17449),(17262,17450),(17263,17451),(17264,17452),(17265,17453),(17266,17454),(17267,17455),(17268,17456),(17269,17457),(17270,17458),(17271,17459),(17272,17460),(17273,17461),(17274,17462),(17275,17463),(17276,17464),(17277,17465),(17278,17466),(17279,17467),(17280,17468),(17281,17469),(17282,17470),(17283,17471),(17284,17472),(17285,17473),(17286,17474),(17287,17475),(17288,17476),(17289,17477),(17290,17478),(17291,17479),(17292,17480),(17293,17481),(17294,17482),(17295,17483),(17296,17484),(17297,17485),(17298,17486),(17299,17487),(17300,17488),(17301,17489),(17302,17490),(17303,17491),(17304,17492),(17305,17493),(17306,17494),(17307,17495),(17308,17496),(17309,17497),(17310,17498),(17311,17499),(17312,17500),(17313,17501),(17314,17502),(17315,17503),(17316,17504),(17317,17505),(17318,17506),(17319,17507),(17320,17508),(17321,17509),(17322,17510),(17323,17511),(17324,17512),(17325,17513),(17326,17514),(17327,17515),(17328,17516),(17329,17517),(17330,17518),(17331,17519),(17332,17520),(17333,17521),(17334,17522),(17335,17523),(17336,17524),(17337,17525),(17338,17526),(17339,17527),(17340,17528),(17341,17529),(17342,17530),(17343,17531),(17344,17532),(17345,17533),(17346,17534),(17347,17535),(17348,17536),(17349,17537),(17350,17538),(17351,17539),(17352,17540),(17353,17541),(17354,17542),(17355,17543),(17356,17544),(17357,17545),(17358,17546),(17359,17547),(17360,17548),(17361,17549),(17362,17550),(17363,17551),(17364,17552),(17365,17553),(17366,17554),(17367,17555),(17368,17556),(17369,17557),(17370,17558),(17371,17559),(17372,17560),(17373,17561),(17374,17562),(17375,17563),(17376,17564),(17377,17565),(17378,17566),(17379,17567),(17380,17568),(17381,17569),(17382,17570),(17383,17571),(17384,17572),(17385,17573),(17386,17574),(17387,17575),(17388,17576),(17389,17577),(17390,17578),(17391,17579),(17392,17580),(17393,17581),(17394,17582),(17395,17583),(17396,17584),(17397,17585),(17398,17586),(17399,17587),(17400,17588),(17401,17589),(17402,17590),(17403,17591),(17404,17592),(17405,17593),(17406,17594),(17407,17595)]
theorem count : slots.length=181 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0067

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0067.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0067.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0067.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0067.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0067.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0067.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0067.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0067.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0067.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0067.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0067.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0067.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0067.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0067.sound
