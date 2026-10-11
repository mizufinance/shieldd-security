import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0087
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(22304,22232),(22305,22233),(22306,22234),(22307,22235),(22308,22236),(22309,22237),(22310,22238),(22311,22239),(22312,22240),(22313,22241),(22314,22242),(22315,22243),(22316,22244),(22317,22245),(22318,22246),(22319,22247),(22320,22248),(22321,22249),(22322,22250),(22323,22251),(22324,22252),(22325,22253),(22326,22254),(22327,22255),(22328,22256),(22329,22257),(22330,22258),(22331,22259),(22332,22260),(22333,22261),(22334,22262),(22335,22263),(22336,22264),(22337,22265),(22338,22266),(22339,22267),(22340,22268),(22341,22269),(22342,22270),(22343,22271),(22344,22272),(22345,22273),(22346,22274),(22347,22275),(22348,22276),(22349,22277),(22350,22278),(22351,22279),(22352,22280),(22353,22281),(22354,22282),(22355,22283),(22356,22284),(22357,22285),(22358,22286),(22359,22287),(22360,22288),(22361,22289),(22362,22290),(22363,22291),(22364,22292),(22365,22293),(22366,22294),(22367,22295),(22368,22296),(22369,22297),(22370,22298),(22371,22299),(22372,22300),(22373,22301),(22374,22302),(22375,22303),(22376,22304),(22377,22305),(22378,22306),(22379,22307),(22380,22308),(22381,22309),(22382,22310),(22383,22311),(22384,22312),(22385,22313),(22386,22314),(22387,22315),(22388,22316),(22389,22317),(22390,22318),(22391,22319),(22392,22320),(22393,22321),(22394,22322),(22395,22323),(22396,22324),(22397,22325),(22398,22326),(22399,22327),(22400,22328),(22401,22329),(22402,22330),(22403,22331),(22404,22332),(22405,22333),(22406,22334),(22407,22335),(22408,22336),(22409,22337),(22410,22338),(22411,22339),(22412,22340),(22413,22341),(22414,22342),(22415,22343),(22416,22344),(22417,22345),(22418,22346),(22419,22347),(22420,22348),(22421,22349),(22422,22350),(22423,22351),(22424,22352),(22425,22353),(22426,22354),(22427,22355),(22428,22356),(22429,22357),(22430,22358),(22431,22359),(22432,22360),(22433,22361),(22434,22362),(22435,22363),(22436,22364),(22437,22365),(22438,22366),(22439,22367),(22440,22368),(22441,22369),(22442,22370),(22443,22371),(22444,22372),(22445,22373),(22446,22374),(22447,22375),(22448,22376),(22449,22377),(22450,22378),(22451,22379),(22452,22380),(22453,22381),(22454,22382),(22455,22383),(22456,22384),(22457,22385),(22458,22386),(22459,22387),(22460,22388),(22461,22389),(22462,22390),(22463,22391),(22464,22392),(22465,22393),(22466,22394),(22467,22395),(22468,22396),(22469,22397),(22470,22398),(22471,22399),(22472,22400),(22473,22401),(22474,22402),(22475,22403),(22476,22404),(22477,22405),(22478,22406),(22479,22407),(22480,22408),(22481,22409),(22482,22410),(22483,22411),(22484,22412),(22485,22413),(22486,22414),(22487,22415),(22488,22416),(22489,22417),(22490,22418),(22491,22419),(22492,22420),(22493,22421),(22494,22422),(22495,22423),(22496,22424),(22497,22425),(22498,22426),(22499,22427),(22500,22428),(22501,22429),(22502,22430),(22503,22431),(22504,22432),(22505,22433),(22506,22434),(22507,22435),(22508,22436),(22509,22437),(22510,22438),(22511,22439),(22512,22440),(22513,22441),(22514,22442),(22515,22443),(22516,22444),(22517,22445),(22518,22446),(22519,22447),(22520,22448),(22521,22449),(22522,22450),(22523,22451),(22524,22452),(22525,22453),(22526,22454),(22527,22455)]
theorem count : slots.length=224 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0087

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0087.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0087.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0087.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0087.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0087.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0087.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0087.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0087.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0087.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0087.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0087.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0087.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0087.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0087.sound
