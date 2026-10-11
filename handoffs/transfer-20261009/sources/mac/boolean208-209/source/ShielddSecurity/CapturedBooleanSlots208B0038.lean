import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0038
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(9859,10084),(9860,10085),(9861,10086),(9862,10087),(9863,10088),(9864,10089),(9865,10090),(9866,10091),(9867,10092),(9868,10093),(9869,10094),(9870,10095),(9871,10096),(9872,10097),(9873,10098),(9874,10099),(9875,10100),(9876,10101),(9877,10102),(9878,10103),(9879,10104),(9880,10105),(9881,10106),(9882,10107),(9883,10108),(9884,10109),(9885,10110),(9886,10111),(9887,10112),(9888,10113),(9889,10114),(9890,10115),(9891,10116),(9892,10117),(9893,10118),(9894,10119),(9895,10120),(9896,10121),(9897,10122),(9898,10123),(9899,10124),(9900,10125),(9901,10126),(9902,10127),(9903,10128),(9904,10129),(9905,10130),(9906,10131),(9907,10132),(9908,10133),(9909,10134),(9910,10135),(9911,10136),(9912,10137),(9913,10138),(9914,10139),(9915,10140),(9916,10141),(9917,10142),(9918,10143),(9919,10144),(9920,10145),(9921,10146),(9922,10147),(9923,10148),(9924,10149),(9925,10150),(9926,10151),(9927,10152),(9928,10153),(9929,10154),(9930,10155),(9931,10156),(9932,10157),(9933,10158),(9934,10159),(9935,10160),(9936,10161),(9937,10162),(9938,10163),(9939,10164),(9940,10165),(9941,10166),(9942,10167),(9943,10168),(9944,10169),(9945,10170),(9946,10171),(9947,10172),(9948,10173),(9949,10174),(9950,10175),(9951,10176),(9952,10177),(9953,10178),(9954,10179),(9955,10180),(9956,10181),(9957,10182),(9958,10183),(9959,10184),(9960,10185),(9961,10186),(9962,10187),(9963,10188),(9964,10189),(9965,10190),(9966,10191),(9967,10192),(9968,10193),(9969,10194),(9970,10195),(9971,10196),(9972,10197),(9973,10198),(9974,10199),(9975,10200),(9976,10201),(9977,10202),(9978,10203),(9979,10204),(9980,10205),(9981,10206),(9982,10207),(9983,10208)]
theorem count : slots.length=125 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0038

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0038.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0038.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0038.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0038.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0038.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0038.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0038.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0038.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0038.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0038.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0038.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0038.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0038.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0038.sound
