import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0072
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(18432,18605),(18433,18606),(18434,18607),(18435,18608),(18436,18609),(18437,18610),(18438,18611),(18439,18612),(18440,18613),(18441,18614),(18442,18615),(18443,18616),(18444,18617),(18445,18618),(18446,18619),(18447,18620),(18448,18621),(18449,18622),(18450,18623),(18451,18624),(18452,18625),(18453,18626),(18454,18627),(18455,18628),(18456,18629),(18457,18630),(18458,18631),(18459,18632),(18460,18633),(18461,18634),(18462,18635),(18463,18636),(18464,18637),(18465,18638),(18466,18639),(18467,18640),(18468,18641),(18469,18642),(18470,18643),(18471,18644),(18472,18645),(18473,18646),(18474,18647),(18475,18648),(18476,18649),(18477,18650),(18478,18651),(18479,18652),(18480,18653),(18481,18654),(18482,18655),(18483,18656),(18484,18657),(18485,18658),(18486,18659),(18487,18660),(18488,18661),(18489,18662),(18490,18663),(18491,18664),(18492,18665),(18493,18666),(18494,18667),(18495,18668),(18496,18669),(18497,18670),(18498,18671),(18499,18672),(18500,18673),(18501,18674),(18502,18675),(18503,18676),(18504,18677),(18505,18678),(18506,18679),(18507,18680),(18508,18681),(18509,18682),(18510,18683),(18511,18684),(18512,18685),(18513,18686),(18514,18687),(18515,18688),(18516,18689),(18520,18690),(18521,18691),(18522,18692),(18523,18693),(18524,18694),(18525,18695),(18526,18696),(18527,18697),(18528,18698),(18529,18699),(18530,18700),(18531,18701),(18532,18702),(18533,18703),(18534,18704),(18535,18705),(18536,18706),(18537,18707),(18538,18708),(18539,18709),(18540,18710),(18541,18711),(18542,18712),(18543,18713),(18544,18714),(18545,18715),(18546,18716),(18547,18717),(18548,18718),(18549,18719),(18550,18720),(18551,18721),(18552,18722),(18553,18723),(18554,18724),(18555,18725),(18556,18726),(18557,18727),(18558,18728),(18559,18729),(18560,18730),(18561,18731),(18562,18732),(18563,18733),(18564,18734),(18565,18735),(18566,18736),(18567,18737),(18568,18738),(18569,18739),(18570,18740),(18571,18741),(18572,18742),(18573,18743),(18574,18744),(18575,18745),(18576,18746),(18577,18747),(18578,18748),(18579,18749),(18580,18750),(18581,18751),(18582,18752),(18583,18753),(18584,18754),(18585,18755),(18586,18756),(18587,18757),(18588,18758),(18589,18759),(18590,18760),(18591,18761),(18592,18762),(18593,18763),(18594,18764),(18595,18765),(18596,18766),(18597,18767),(18598,18768),(18599,18769),(18600,18770),(18601,18771),(18602,18772),(18603,18773),(18604,18774),(18605,18775),(18606,18776),(18607,18777),(18608,18778),(18609,18779),(18610,18780),(18611,18781),(18612,18782),(18613,18783),(18614,18784),(18615,18785),(18616,18786),(18617,18787),(18618,18788),(18619,18789),(18620,18790),(18621,18791),(18622,18792),(18623,18793),(18624,18794),(18625,18795),(18626,18796),(18627,18797),(18628,18798),(18629,18799),(18630,18800),(18631,18801),(18632,18802),(18633,18803),(18634,18804),(18635,18805),(18636,18806),(18637,18807),(18638,18808),(18639,18809),(18640,18810),(18641,18811),(18642,18812),(18643,18813),(18644,18814),(18645,18815),(18646,18816),(18647,18817),(18648,18818),(18649,18819),(18650,18820),(18651,18821),(18652,18822),(18653,18823),(18654,18824),(18655,18825),(18656,18826),(18657,18827),(18658,18828),(18659,18829),(18660,18830),(18661,18831),(18662,18832),(18663,18833),(18664,18834),(18665,18835),(18666,18836),(18667,18837),(18668,18838),(18669,18839),(18670,18840),(18671,18841),(18672,18842),(18673,18843),(18674,18844),(18675,18845),(18676,18846),(18677,18847),(18678,18848),(18679,18849),(18680,18850),(18681,18851),(18682,18852),(18683,18853),(18684,18854),(18685,18855),(18686,18856),(18687,18857)]
theorem count : slots.length=253 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0072

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0072.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0072.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0072.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0072.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0072.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0072.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0072.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0072.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0072.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0072.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0072.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0072.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0072.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0072.sound
