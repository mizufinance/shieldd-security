import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0073
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(18688,18858),(18689,18859),(18690,18860),(18691,18861),(18692,18862),(18693,18863),(18694,18864),(18695,18865),(18696,18866),(18697,18867),(18698,18868),(18699,18869),(18700,18870),(18701,18871),(18702,18872),(18703,18873),(18704,18874),(18705,18875),(18706,18876),(18707,18877),(18708,18878),(18709,18879),(18710,18880),(18711,18881),(18712,18882),(18713,18883),(18714,18884),(18715,18885),(18716,18886),(18717,18887),(18718,18888),(18719,18889),(18720,18890),(18721,18891),(18722,18892),(18723,18893),(18724,18894),(18725,18895),(18726,18896),(18727,18897),(18728,18898),(18729,18899),(18730,18900),(18731,18901),(18732,18902),(18733,18903),(18734,18904),(18735,18905),(18736,18906),(18737,18907),(18738,18908),(18739,18909),(18740,18910),(18741,18911),(18742,18912),(18743,18913),(18744,18914),(18745,18915),(18746,18916),(18747,18917),(18748,18918),(18749,18919),(18750,18920),(18751,18921),(18752,18922),(18753,18923),(18754,18924),(18755,18925),(18756,18926),(18757,18927),(18758,18928),(18759,18929),(18760,18930),(18761,18931),(18762,18932),(18763,18933),(18764,18934),(18765,18935),(18766,18936),(18767,18937),(18768,18938),(18769,18939),(18770,18940),(18771,18941),(18772,18942),(18773,18943),(18774,18944),(18778,18945),(18779,18946),(18780,18947),(18781,18948),(18782,18949),(18783,18950),(18784,18951),(18785,18952),(18786,18953),(18787,18954),(18788,18955),(18789,18956),(18790,18957),(18791,18958),(18792,18959),(18793,18960),(18794,18961),(18795,18962),(18796,18963),(18797,18964),(18798,18965),(18799,18966),(18800,18967),(18801,18968),(18802,18969),(18803,18970),(18804,18971),(18805,18972),(18806,18973),(18807,18974),(18808,18975),(18809,18976),(18810,18977),(18811,18978),(18812,18979),(18813,18980),(18814,18981),(18815,18982),(18816,18983),(18817,18984),(18818,18985),(18819,18986),(18820,18987),(18821,18988),(18822,18989),(18823,18990),(18824,18991),(18825,18992),(18826,18993),(18827,18994),(18828,18995),(18829,18996),(18830,18997),(18831,18998),(18832,18999),(18833,19000),(18834,19001),(18835,19002),(18836,19003),(18837,19004),(18838,19005),(18839,19006),(18840,19007),(18841,19008),(18842,19009),(18843,19010),(18844,19011),(18845,19012),(18846,19013),(18847,19014),(18848,19015),(18849,19016),(18850,19017),(18851,19018),(18852,19019),(18853,19020),(18854,19021),(18855,19022),(18856,19023),(18857,19024),(18858,19025),(18859,19026),(18860,19027),(18861,19028),(18862,19029),(18863,19030),(18864,19031),(18865,19032),(18866,19033),(18867,19034),(18868,19035),(18869,19036),(18870,19037),(18871,19038),(18872,19039),(18873,19040),(18874,19041),(18875,19042),(18876,19043),(18877,19044),(18878,19045),(18879,19046),(18880,19047),(18881,19048),(18882,19049),(18883,19050),(18884,19051),(18885,19052),(18886,19053),(18887,19054),(18888,19055),(18889,19056),(18890,19057),(18891,19058),(18892,19059),(18893,19060),(18894,19061),(18895,19062),(18896,19063),(18897,19064),(18898,19065),(18899,19066),(18900,19067),(18901,19068),(18902,19069),(18903,19070),(18904,19071),(18905,19072),(18906,19073),(18907,19074),(18908,19075),(18909,19076),(18910,19077),(18911,19078),(18912,19079),(18913,19080),(18914,19081),(18915,19082),(18916,19083),(18917,19084),(18918,19085),(18919,19086),(18920,19087),(18921,19088),(18922,19089),(18923,19090),(18924,19091),(18925,19092),(18926,19093),(18927,19094),(18928,19095),(18929,19096),(18930,19097),(18931,19098),(18932,19099),(18933,19100),(18934,19101),(18935,19102),(18936,19103),(18937,19104),(18938,19105),(18939,19106),(18940,19107),(18941,19108),(18942,19109),(18943,19110)]
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
end ShielddSecurity.CapturedBooleanSlots208B0073

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0073.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0073.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0073.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0073.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0073.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0073.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0073.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0073.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0073.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0073.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0073.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0073.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0073.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0073.sound
