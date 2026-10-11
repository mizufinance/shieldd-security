import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0079
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(20224,20237),(20225,20238),(20226,20239),(20227,20240),(20228,20241),(20229,20242),(20230,20243),(20231,20244),(20232,20245),(20233,20246),(20234,20247),(20235,20248),(20236,20249),(20237,20250),(20238,20251),(20239,20252),(20240,20253),(20241,20254),(20242,20255),(20243,20256),(20244,20257),(20245,20258),(20246,20259),(20247,20260),(20248,20261),(20249,20262),(20250,20263),(20251,20264),(20252,20265),(20253,20266),(20254,20267),(20255,20268),(20256,20269),(20257,20270),(20258,20271),(20259,20272),(20260,20273),(20261,20274),(20262,20275),(20263,20276),(20264,20277),(20265,20278),(20266,20279),(20267,20280),(20268,20281),(20269,20282),(20270,20283),(20271,20284),(20272,20285),(20273,20286),(20274,20287),(20275,20288),(20276,20289),(20277,20290),(20278,20291),(20279,20292),(20280,20293),(20281,20294),(20282,20295),(20283,20296),(20284,20297),(20285,20298),(20286,20299),(20287,20300),(20288,20301),(20289,20302),(20290,20303),(20291,20304),(20292,20305),(20293,20306),(20294,20307),(20295,20308),(20296,20309),(20297,20310),(20298,20311),(20299,20312),(20300,20313),(20301,20314),(20302,20315),(20303,20316),(20304,20317),(20305,20318),(20306,20319),(20307,20320),(20308,20321),(20309,20322),(20310,20323),(20311,20324),(20312,20325),(20313,20326),(20314,20327),(20315,20328),(20316,20329),(20317,20330),(20318,20331),(20319,20332),(20320,20333),(20321,20334),(20322,20335),(20323,20336),(20324,20337),(20325,20338),(20326,20339),(20327,20340),(20328,20341),(20329,20342),(20330,20343),(20331,20344),(20332,20345),(20333,20346),(20334,20347),(20335,20348),(20336,20349),(20337,20350),(20338,20351),(20339,20352),(20340,20353),(20341,20354),(20342,20355),(20343,20356),(20344,20357),(20345,20358),(20346,20359),(20347,20360),(20348,20361),(20349,20362),(20350,20363),(20351,20364),(20352,20365),(20353,20366),(20354,20367),(20355,20368),(20356,20369),(20357,20370),(20358,20371),(20359,20372),(20360,20373),(20361,20374),(20362,20375),(20363,20376),(20364,20377),(20365,20378),(20366,20379),(20367,20380),(20368,20381),(20369,20382),(20370,20383),(20371,20384),(20372,20385),(20373,20386),(20374,20387),(20375,20388),(20376,20389),(20377,20390),(20378,20391),(20414,20392),(20415,20393),(20416,20394),(20417,20395),(20418,20396),(20419,20397),(20420,20398),(20421,20399),(20422,20400),(20423,20401),(20424,20402),(20425,20403),(20426,20404),(20427,20405),(20428,20406),(20429,20407),(20430,20408),(20431,20409),(20432,20410),(20433,20411),(20434,20412),(20435,20413),(20436,20414),(20437,20415),(20438,20416),(20439,20417),(20440,20418),(20441,20419),(20442,20420),(20443,20421),(20444,20422),(20445,20423),(20447,20424),(20448,20425),(20449,20426),(20450,20427),(20451,20428),(20452,20429),(20453,20430),(20454,20431),(20455,20432),(20456,20433),(20457,20434),(20458,20435),(20459,20436),(20460,20437),(20461,20438),(20462,20439),(20463,20440),(20464,20441),(20465,20442),(20466,20443),(20467,20444),(20468,20445),(20469,20446),(20470,20447),(20471,20448),(20472,20449),(20473,20450),(20474,20451),(20475,20452),(20476,20453),(20477,20454),(20478,20455),(20479,20456)]
theorem count : slots.length=220 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0079

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0079.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0079.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0079.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0079.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0079.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0079.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0079.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0079.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0079.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0079.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0079.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0079.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0079.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0079.sound
