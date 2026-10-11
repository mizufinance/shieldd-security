import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0080
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(20480,20457),(20481,20458),(20482,20459),(20483,20460),(20484,20461),(20485,20462),(20486,20463),(20487,20464),(20488,20465),(20489,20466),(20490,20467),(20491,20468),(20492,20469),(20493,20470),(20494,20471),(20495,20472),(20496,20473),(20497,20474),(20498,20475),(20499,20476),(20500,20477),(20501,20478),(20502,20479),(20503,20480),(20504,20481),(20505,20482),(20506,20483),(20507,20484),(20508,20485),(20509,20486),(20510,20487),(20511,20488),(20512,20489),(20513,20490),(20514,20491),(20515,20492),(20516,20493),(20517,20494),(20518,20495),(20519,20496),(20520,20497),(20521,20498),(20522,20499),(20523,20500),(20524,20501),(20525,20502),(20526,20503),(20527,20504),(20528,20505),(20529,20506),(20530,20507),(20531,20508),(20532,20509),(20533,20510),(20534,20511),(20535,20512),(20536,20513),(20537,20514),(20538,20515),(20539,20516),(20540,20517),(20541,20518),(20542,20519),(20543,20520),(20544,20521),(20545,20522),(20546,20523),(20547,20524),(20548,20525),(20549,20526),(20550,20527),(20551,20528),(20552,20529),(20553,20530),(20554,20531),(20555,20532),(20556,20533),(20557,20534),(20558,20535),(20559,20536),(20560,20537),(20561,20538),(20562,20539),(20563,20540),(20564,20541),(20565,20542),(20566,20543),(20567,20544),(20568,20545),(20569,20546),(20570,20547),(20571,20548),(20572,20549),(20573,20550),(20574,20551),(20575,20552),(20576,20553),(20577,20554),(20578,20555),(20579,20556),(20580,20557),(20581,20558),(20582,20559),(20583,20560),(20584,20561),(20585,20562),(20586,20563),(20587,20564),(20588,20565),(20589,20566),(20590,20567),(20591,20568),(20592,20569),(20593,20570),(20594,20571),(20595,20572),(20596,20573),(20597,20574),(20598,20575),(20599,20576),(20600,20577),(20601,20578),(20602,20579),(20603,20580),(20604,20581),(20605,20582),(20606,20583),(20607,20584),(20608,20585),(20609,20586),(20610,20587),(20611,20588),(20612,20589),(20613,20590),(20614,20591),(20615,20592),(20616,20593),(20617,20594),(20618,20595),(20619,20596),(20620,20597),(20621,20598),(20622,20599),(20623,20600),(20624,20601),(20625,20602),(20626,20603),(20627,20604),(20628,20605),(20629,20606),(20630,20607),(20631,20608),(20632,20609),(20633,20610),(20634,20611),(20635,20612),(20636,20613),(20637,20614),(20638,20615),(20639,20616),(20640,20617),(20641,20618),(20642,20619),(20643,20620),(20644,20621),(20645,20622),(20646,20623),(20647,20624),(20648,20625),(20649,20626),(20650,20627),(20651,20628),(20652,20629),(20653,20630),(20654,20631),(20655,20632),(20656,20633),(20657,20634),(20658,20635),(20659,20636),(20660,20637),(20661,20638),(20662,20639),(20663,20640),(20664,20641),(20665,20642),(20666,20643),(20667,20644),(20668,20645),(20669,20646),(20670,20647),(20671,20648),(20672,20649),(20673,20650),(20674,20651),(20675,20652),(20676,20653),(20677,20654),(20678,20655),(20679,20656),(20680,20657),(20681,20658),(20682,20659),(20683,20660),(20684,20661),(20685,20662),(20686,20663),(20687,20664),(20688,20665),(20689,20666),(20690,20667),(20691,20668),(20692,20669),(20693,20670),(20694,20671),(20695,20672),(20696,20673),(20697,20674),(20698,20675),(20699,20676),(20700,20677),(20701,20678),(20705,20679),(20706,20680),(20707,20681),(20708,20682),(20709,20683),(20710,20684),(20711,20685),(20712,20686),(20713,20687),(20714,20688),(20715,20689),(20716,20690),(20717,20691),(20718,20692),(20719,20693),(20720,20694),(20721,20695),(20722,20696),(20723,20697),(20724,20698),(20725,20699),(20726,20700),(20727,20701),(20728,20702),(20729,20703),(20730,20704),(20731,20705),(20732,20706),(20733,20707),(20734,20708),(20735,20709)]
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
end ShielddSecurity.CapturedBooleanSlots208B0080

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0080.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0080.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0080.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0080.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0080.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0080.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0080.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0080.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0080.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0080.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0080.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0080.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0080.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0080.sound
