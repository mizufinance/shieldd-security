import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0084
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(21504,21436),(21505,21437),(21506,21438),(21507,21439),(21508,21440),(21509,21441),(21510,21442),(21511,21443),(21512,21444),(21513,21445),(21514,21446),(21515,21447),(21516,21448),(21517,21449),(21518,21450),(21519,21451),(21520,21452),(21521,21453),(21522,21454),(21524,21455),(21525,21456),(21526,21457),(21527,21458),(21528,21459),(21529,21460),(21530,21461),(21531,21462),(21532,21463),(21533,21464),(21534,21465),(21535,21466),(21536,21467),(21537,21468),(21538,21469),(21539,21470),(21540,21471),(21541,21472),(21542,21473),(21543,21474),(21544,21475),(21545,21476),(21546,21477),(21547,21478),(21548,21479),(21549,21480),(21550,21481),(21551,21482),(21552,21483),(21553,21484),(21554,21485),(21555,21486),(21556,21487),(21557,21488),(21558,21489),(21559,21490),(21560,21491),(21561,21492),(21562,21493),(21563,21494),(21564,21495),(21565,21496),(21566,21497),(21567,21498),(21568,21499),(21569,21500),(21570,21501),(21571,21502),(21572,21503),(21573,21504),(21574,21505),(21575,21506),(21576,21507),(21577,21508),(21578,21509),(21579,21510),(21580,21511),(21581,21512),(21582,21513),(21583,21514),(21584,21515),(21585,21516),(21586,21517),(21587,21518),(21588,21519),(21589,21520),(21590,21521),(21591,21522),(21592,21523),(21593,21524),(21594,21525),(21595,21526),(21596,21527),(21597,21528),(21598,21529),(21599,21530),(21600,21531),(21601,21532),(21602,21533),(21603,21534),(21604,21535),(21605,21536),(21606,21537),(21607,21538),(21608,21539),(21609,21540),(21610,21541),(21611,21542),(21612,21543),(21613,21544),(21614,21545),(21615,21546),(21616,21547),(21617,21548),(21618,21549),(21619,21550),(21620,21551),(21621,21552),(21622,21553),(21623,21554),(21624,21555),(21625,21556),(21626,21557),(21627,21558),(21628,21559),(21629,21560),(21630,21561),(21631,21562),(21632,21563),(21633,21564),(21634,21565),(21635,21566),(21636,21567),(21637,21568),(21638,21569),(21639,21570),(21640,21571),(21641,21572),(21642,21573),(21643,21574),(21644,21575),(21645,21576),(21646,21577),(21647,21578),(21648,21579),(21649,21580),(21650,21581),(21651,21582),(21653,21583),(21654,21584),(21655,21585),(21656,21586),(21657,21587),(21658,21588),(21659,21589),(21660,21590),(21661,21591),(21662,21592),(21663,21593),(21664,21594),(21665,21595),(21666,21596),(21667,21597),(21668,21598),(21669,21599),(21670,21600),(21671,21601),(21672,21602),(21673,21603),(21674,21604),(21675,21605),(21676,21606),(21677,21607),(21678,21608),(21679,21609),(21680,21610),(21681,21611),(21682,21612),(21683,21613),(21684,21614),(21685,21615),(21686,21616),(21687,21617),(21688,21618),(21689,21619),(21690,21620),(21691,21621),(21692,21622),(21693,21623),(21694,21624),(21695,21625),(21696,21626),(21697,21627),(21698,21628),(21699,21629),(21700,21630),(21701,21631),(21702,21632),(21703,21633),(21704,21634),(21705,21635),(21706,21636),(21707,21637),(21708,21638),(21709,21639),(21710,21640),(21711,21641),(21712,21642),(21713,21643),(21714,21644),(21715,21645),(21716,21646),(21717,21647),(21718,21648),(21719,21649),(21720,21650),(21721,21651),(21722,21652),(21723,21653),(21724,21654),(21725,21655),(21726,21656),(21727,21657),(21728,21658),(21729,21659),(21730,21660),(21731,21661),(21732,21662),(21733,21663),(21734,21664),(21735,21665),(21736,21666),(21737,21667),(21738,21668),(21739,21669),(21740,21670),(21741,21671),(21742,21672),(21743,21673),(21744,21674),(21745,21675),(21746,21676),(21747,21677),(21748,21678),(21749,21679),(21750,21680),(21751,21681),(21752,21682),(21753,21683),(21754,21684),(21755,21685),(21756,21686),(21757,21687),(21758,21688),(21759,21689)]
theorem count : slots.length=254 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0084

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0084.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0084.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0084.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0084.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0084.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0084.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0084.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0084.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0084.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0084.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0084.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0084.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0084.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0084.sound
