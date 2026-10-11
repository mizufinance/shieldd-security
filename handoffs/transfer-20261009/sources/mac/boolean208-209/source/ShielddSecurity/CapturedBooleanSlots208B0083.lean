import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0083
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(21248,21187),(21249,21188),(21250,21189),(21251,21190),(21252,21191),(21253,21192),(21258,21193),(21266,21199),(21267,21200),(21268,21201),(21269,21202),(21270,21203),(21271,21204),(21272,21205),(21273,21206),(21274,21207),(21275,21208),(21276,21209),(21277,21210),(21278,21211),(21279,21212),(21280,21213),(21281,21214),(21282,21215),(21283,21216),(21284,21217),(21285,21218),(21286,21219),(21287,21220),(21288,21221),(21289,21222),(21290,21223),(21291,21224),(21292,21225),(21293,21226),(21294,21227),(21295,21228),(21296,21229),(21297,21230),(21298,21231),(21299,21232),(21300,21233),(21301,21234),(21302,21235),(21303,21236),(21304,21237),(21305,21238),(21306,21239),(21307,21240),(21308,21241),(21309,21242),(21310,21243),(21311,21244),(21312,21245),(21313,21246),(21314,21247),(21315,21248),(21316,21249),(21317,21250),(21318,21251),(21319,21252),(21320,21253),(21321,21254),(21322,21255),(21323,21256),(21324,21257),(21325,21258),(21326,21259),(21327,21260),(21328,21261),(21329,21262),(21330,21263),(21331,21264),(21332,21265),(21333,21266),(21334,21267),(21335,21268),(21336,21269),(21337,21270),(21338,21271),(21339,21272),(21340,21273),(21341,21274),(21342,21275),(21343,21276),(21344,21277),(21345,21278),(21346,21279),(21347,21280),(21348,21281),(21349,21282),(21350,21283),(21351,21284),(21352,21285),(21353,21286),(21354,21287),(21355,21288),(21356,21289),(21357,21290),(21358,21291),(21359,21292),(21360,21293),(21361,21294),(21362,21295),(21363,21296),(21364,21297),(21365,21298),(21366,21299),(21367,21300),(21368,21301),(21369,21302),(21370,21303),(21371,21304),(21372,21305),(21373,21306),(21374,21307),(21375,21308),(21376,21309),(21377,21310),(21378,21311),(21379,21312),(21380,21313),(21381,21314),(21382,21315),(21383,21316),(21384,21317),(21385,21318),(21386,21319),(21387,21320),(21388,21321),(21389,21322),(21390,21323),(21391,21324),(21392,21325),(21393,21326),(21395,21327),(21396,21328),(21397,21329),(21398,21330),(21399,21331),(21400,21332),(21401,21333),(21402,21334),(21403,21335),(21404,21336),(21405,21337),(21406,21338),(21407,21339),(21408,21340),(21409,21341),(21410,21342),(21411,21343),(21412,21344),(21413,21345),(21414,21346),(21415,21347),(21416,21348),(21417,21349),(21418,21350),(21419,21351),(21420,21352),(21421,21353),(21422,21354),(21423,21355),(21424,21356),(21425,21357),(21426,21358),(21427,21359),(21428,21360),(21429,21361),(21430,21362),(21431,21363),(21432,21364),(21433,21365),(21434,21366),(21435,21367),(21436,21368),(21437,21369),(21438,21370),(21439,21371),(21440,21372),(21441,21373),(21442,21374),(21443,21375),(21444,21376),(21445,21377),(21446,21378),(21447,21379),(21448,21380),(21449,21381),(21450,21382),(21451,21383),(21452,21384),(21453,21385),(21454,21386),(21455,21387),(21456,21388),(21457,21389),(21458,21390),(21459,21391),(21460,21392),(21461,21393),(21462,21394),(21463,21395),(21464,21396),(21465,21397),(21466,21398),(21467,21399),(21468,21400),(21469,21401),(21470,21402),(21471,21403),(21472,21404),(21473,21405),(21474,21406),(21475,21407),(21476,21408),(21477,21409),(21478,21410),(21479,21411),(21480,21412),(21481,21413),(21482,21414),(21483,21415),(21484,21416),(21485,21417),(21486,21418),(21487,21419),(21488,21420),(21489,21421),(21490,21422),(21491,21423),(21492,21424),(21493,21425),(21494,21426),(21495,21427),(21496,21428),(21497,21429),(21498,21430),(21499,21431),(21500,21432),(21501,21433),(21502,21434),(21503,21435)]
theorem count : slots.length=244 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0083

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0083.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0083.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0083.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0083.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0083.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0083.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0083.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0083.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0083.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0083.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0083.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0083.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0083.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0083.sound
