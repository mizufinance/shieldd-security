import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0076
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(19458,19557),(19461,19559),(19464,19561),(19467,19563),(19470,19565),(19473,19567),(19476,19569),(19479,19571),(19482,19573),(19485,19575),(19488,19577),(19491,19579),(19494,19581),(19497,19583),(19500,19585),(19503,19587),(19572,19591),(19573,19592),(19574,19593),(19575,19594),(19576,19595),(19577,19596),(19578,19597),(19579,19598),(19580,19599),(19581,19600),(19582,19601),(19583,19602),(19584,19603),(19585,19604),(19586,19605),(19587,19606),(19588,19607),(19589,19608),(19590,19609),(19591,19610),(19592,19611),(19593,19612),(19594,19613),(19595,19614),(19596,19615),(19597,19616),(19598,19617),(19599,19618),(19600,19619),(19601,19620),(19602,19621),(19603,19622),(19604,19623),(19605,19624),(19606,19625),(19607,19626),(19608,19627),(19609,19628),(19610,19629),(19611,19630),(19612,19631),(19613,19632),(19614,19633),(19615,19634),(19616,19635),(19617,19636),(19618,19637),(19619,19638),(19620,19639),(19621,19640),(19622,19641),(19623,19642),(19624,19643),(19625,19644),(19626,19645),(19627,19646),(19628,19647),(19629,19648),(19630,19649),(19631,19650),(19632,19651),(19633,19652),(19634,19653),(19635,19654),(19636,19655),(19637,19656),(19638,19657),(19639,19658),(19640,19659),(19641,19660),(19642,19661),(19643,19662),(19644,19663),(19645,19664),(19646,19665),(19647,19666),(19648,19667),(19649,19668),(19650,19669),(19651,19670),(19652,19671),(19653,19672),(19654,19673),(19655,19674),(19656,19675),(19657,19676),(19658,19677),(19659,19678),(19660,19679),(19661,19680),(19662,19681),(19663,19682),(19664,19683),(19665,19684),(19666,19685),(19667,19686),(19668,19687),(19669,19688),(19670,19689),(19671,19690),(19672,19691),(19673,19692),(19674,19693),(19675,19694),(19676,19695),(19677,19696),(19678,19697),(19679,19698),(19680,19699),(19681,19700),(19682,19701),(19683,19702),(19684,19703),(19685,19704),(19686,19705),(19687,19706),(19688,19707),(19689,19708),(19690,19709),(19691,19710),(19692,19711),(19693,19712),(19694,19713),(19695,19714),(19696,19715),(19697,19716),(19698,19717),(19699,19718),(19700,19719),(19701,19720),(19702,19721),(19703,19722),(19704,19723),(19705,19724),(19706,19725),(19707,19726),(19708,19727),(19709,19728),(19710,19729),(19711,19730)]
theorem count : slots.length=156 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0076

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0076.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0076.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0076.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0076.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0076.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0076.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0076.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0076.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0076.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0076.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0076.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0076.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0076.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0076.sound
