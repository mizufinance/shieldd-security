import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0057
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(14687,14892),(14688,14893),(14689,14894),(14690,14895),(14691,14896),(14692,14897),(14693,14898),(14694,14899),(14695,14900),(14696,14901),(14697,14902),(14698,14903),(14699,14904),(14700,14905),(14701,14906),(14702,14907),(14703,14908),(14704,14909),(14705,14910),(14706,14911),(14707,14912),(14708,14913),(14709,14914),(14710,14915),(14711,14916),(14712,14917),(14713,14918),(14714,14919),(14715,14920),(14716,14921),(14717,14922),(14718,14923),(14719,14924),(14720,14925),(14721,14926),(14722,14927),(14723,14928),(14724,14929),(14725,14930),(14726,14931),(14727,14932),(14728,14933),(14729,14934),(14730,14935),(14731,14936),(14732,14937),(14733,14938),(14734,14939),(14735,14940),(14736,14941),(14737,14942),(14738,14943),(14739,14944),(14740,14945),(14741,14946),(14742,14947),(14743,14948),(14744,14949),(14745,14950),(14746,14951),(14747,14952),(14748,14953),(14749,14954),(14750,14955),(14751,14956),(14752,14957),(14753,14958),(14754,14959),(14755,14960),(14756,14961),(14757,14962),(14758,14963),(14759,14964),(14760,14965),(14761,14966),(14762,14967),(14763,14968),(14764,14969),(14765,14970),(14766,14971),(14767,14972),(14768,14973),(14769,14974),(14770,14975),(14771,14976),(14772,14977),(14773,14978),(14774,14979),(14775,14980),(14776,14981),(14777,14982),(14778,14983),(14779,14984),(14780,14985),(14781,14986),(14782,14987),(14783,14988),(14784,14989),(14785,14990),(14786,14991),(14787,14992),(14788,14993),(14789,14994),(14790,14995),(14791,14996),(14792,14997),(14793,14998),(14794,14999),(14795,15000),(14796,15001),(14797,15002),(14798,15003),(14799,15004),(14800,15005),(14801,15006),(14802,15007),(14803,15008),(14804,15009),(14805,15010),(14806,15011),(14807,15012),(14808,15013),(14809,15014),(14810,15015),(14811,15016),(14812,15017),(14813,15018),(14814,15019),(14815,15020),(14816,15021),(14817,15022),(14818,15023),(14819,15024),(14820,15025),(14821,15026),(14822,15027),(14823,15028),(14824,15029),(14825,15030),(14826,15031),(14827,15032),(14828,15033),(14829,15034),(14830,15035),(14831,15036),(14832,15037),(14833,15038),(14834,15039),(14835,15040),(14836,15041),(14837,15042),(14838,15043),(14839,15044),(14840,15045),(14841,15046),(14842,15047),(14843,15048),(14844,15049),(14845,15050),(14846,15051),(14847,15052)]
theorem count : slots.length=161 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0057

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0057.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0057.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0057.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0057.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0057.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0057.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0057.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0057.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0057.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0057.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0057.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0057.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0057.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0057.sound
