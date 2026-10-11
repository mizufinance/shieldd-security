import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0085
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(21760,21690),(21761,21691),(21762,21692),(21763,21693),(21764,21694),(21765,21695),(21766,21696),(21767,21697),(21768,21698),(21769,21699),(21770,21700),(21771,21701),(21772,21702),(21773,21703),(21774,21704),(21775,21705),(21776,21706),(21777,21707),(21778,21708),(21779,21709),(21780,21710),(21782,21711),(21783,21713),(21784,21714),(21785,21715),(21786,21716),(21787,21717),(21788,21718),(21789,21719),(21790,21720),(21791,21721),(21792,21722),(21793,21723),(21794,21724),(21795,21725),(21796,21726),(21797,21727),(21798,21728),(21799,21729),(21800,21730),(21801,21731),(21802,21732),(21803,21733),(21804,21734),(21805,21735),(21806,21736),(21807,21737),(21808,21738),(21809,21739),(21810,21740),(21811,21741),(21812,21742),(21813,21743),(21814,21744),(21815,21745),(21816,21746),(21817,21747),(21818,21748),(21819,21749),(21820,21750),(21821,21751),(21822,21752),(21823,21753),(21824,21754),(21825,21755),(21826,21756),(21827,21757),(21828,21758),(21829,21759),(21830,21760),(21831,21761),(21832,21762),(21833,21763),(21834,21764),(21835,21765),(21836,21766),(21837,21767),(21838,21768),(21839,21769),(21840,21770),(21841,21771),(21842,21772),(21843,21773),(21844,21774),(21845,21775),(21846,21776),(21847,21777),(21848,21778),(21849,21779),(21850,21780),(21851,21781),(21852,21782),(21853,21783),(21854,21784),(21855,21785),(21856,21786),(21857,21787),(21858,21788),(21859,21789),(21860,21790),(21861,21791),(21862,21792),(21863,21793),(21864,21794),(21865,21795),(21866,21796),(21867,21797),(21868,21798),(21869,21799),(21870,21800),(21871,21801),(21872,21802),(21873,21803),(21874,21804),(21875,21805),(21876,21806),(21877,21807),(21878,21808),(21879,21809),(21880,21810),(21881,21811),(21882,21812),(21883,21813),(21884,21814),(21885,21815),(21886,21816),(21887,21817),(21888,21818),(21889,21819),(21890,21820),(21891,21821),(21892,21822),(21893,21823),(21894,21824),(21895,21825),(21896,21826),(21897,21827),(21898,21828),(21899,21829),(21900,21830),(21901,21831),(21902,21832),(21903,21833),(21904,21834),(21905,21835),(21906,21836),(21907,21837),(21908,21838),(21909,21839),(21910,21840),(21911,21841)]
theorem count : slots.length=151 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0085

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0085.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0085.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0085.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0085.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0085.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0085.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0085.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0085.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0085.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0085.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0085.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0085.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0085.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0085.sound
