import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0077
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(19712,19731),(19713,19732),(19714,19733),(19715,19734),(19716,19735),(19717,19736),(19718,19737),(19719,19738),(19720,19739),(19721,19740),(19722,19741),(19723,19742),(19724,19743),(19725,19744),(19726,19745),(19727,19746),(19728,19747),(19729,19748),(19730,19749),(19731,19750),(19732,19751),(19733,19752),(19734,19753),(19735,19754),(19736,19755),(19737,19756),(19738,19757),(19739,19758),(19740,19759),(19741,19760),(19742,19761),(19743,19762),(19744,19763),(19745,19764),(19746,19765),(19747,19766),(19748,19767),(19749,19768),(19750,19769),(19751,19770),(19752,19771),(19753,19772),(19754,19773),(19755,19774),(19756,19775),(19757,19776),(19758,19777),(19759,19778),(19760,19779),(19761,19780),(19762,19781),(19763,19782),(19764,19783),(19765,19784),(19766,19785),(19767,19786),(19768,19787),(19769,19788),(19770,19789),(19771,19790),(19772,19791),(19773,19792),(19774,19793),(19775,19794),(19776,19795),(19777,19796),(19778,19797),(19779,19798),(19780,19799),(19781,19800),(19782,19801),(19783,19802),(19784,19803),(19785,19804),(19786,19805),(19787,19806),(19788,19807),(19789,19808),(19790,19809),(19791,19810),(19792,19811),(19793,19812),(19794,19813),(19795,19814),(19796,19815),(19797,19816),(19798,19817),(19799,19818),(19800,19819),(19801,19820),(19802,19821),(19803,19822),(19804,19823),(19805,19824),(19806,19825),(19807,19826),(19808,19827),(19809,19828),(19810,19829),(19811,19830),(19812,19831),(19813,19832),(19814,19833),(19815,19834),(19816,19835),(19817,19836),(19818,19837),(19819,19838),(19820,19839),(19821,19840),(19822,19841),(19823,19842),(19824,19843),(19825,19844),(19826,19845),(19830,19846),(19833,19850),(19834,19851),(19835,19852),(19836,19853),(19837,19854),(19838,19855),(19839,19856),(19840,19857),(19841,19858),(19842,19859),(19843,19860),(19844,19861),(19845,19862),(19846,19863),(19847,19864),(19848,19865),(19849,19866),(19850,19867),(19851,19868),(19852,19869),(19853,19870),(19854,19871),(19855,19872),(19856,19873),(19857,19874),(19858,19875),(19859,19876),(19860,19877),(19861,19878),(19862,19879),(19863,19880),(19864,19881),(19866,19882),(19867,19883),(19868,19884),(19869,19885),(19870,19886),(19871,19887),(19872,19888),(19873,19889),(19874,19890),(19875,19891),(19876,19892),(19877,19893),(19878,19894),(19879,19895),(19880,19896),(19881,19897),(19882,19898),(19883,19899),(19884,19900),(19885,19901),(19886,19902),(19887,19903),(19888,19904),(19889,19905),(19890,19906),(19891,19907),(19892,19908),(19893,19909),(19894,19910),(19895,19911),(19896,19912),(19897,19913),(19898,19914),(19899,19915),(19900,19916),(19901,19917),(19902,19918),(19903,19919),(19904,19920),(19905,19921),(19906,19922),(19907,19923),(19908,19924),(19909,19925),(19910,19926),(19911,19927),(19912,19928),(19913,19929),(19914,19930),(19915,19931),(19916,19932),(19917,19933),(19918,19934),(19919,19935),(19920,19936),(19921,19937),(19922,19938),(19923,19939),(19924,19940),(19925,19941),(19926,19942),(19927,19943),(19928,19944),(19929,19945),(19930,19946),(19931,19947),(19932,19948),(19933,19949),(19934,19950),(19935,19951),(19936,19952),(19937,19953),(19938,19954),(19939,19955),(19940,19956),(19941,19957),(19942,19958),(19943,19959),(19944,19960),(19945,19961),(19946,19962),(19947,19963),(19948,19964),(19949,19965),(19950,19966),(19951,19967),(19952,19968),(19953,19969),(19954,19970),(19955,19971),(19956,19972),(19957,19973),(19958,19974),(19959,19975),(19960,19976),(19961,19977),(19962,19978),(19963,19979),(19964,19980),(19965,19981),(19966,19982),(19967,19983)]
theorem count : slots.length=250 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0077

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0077.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0077.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0077.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0077.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0077.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0077.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0077.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0077.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0077.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0077.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0077.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0077.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0077.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0077.sound
