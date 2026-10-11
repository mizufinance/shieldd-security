import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0034
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(8831,9059),(8834,9062),(8835,9063),(8836,9064),(8837,9065),(8838,9066),(8839,9067),(8840,9068),(8841,9069),(8842,9070),(8843,9071),(8844,9072),(8845,9073),(8846,9074),(8847,9075),(8848,9076),(8849,9077),(8850,9078),(8851,9079),(8852,9080),(8853,9081),(8854,9082),(8855,9083),(8856,9084),(8857,9085),(8858,9086),(8859,9087),(8860,9088),(8861,9089),(8862,9090),(8863,9091),(8864,9092),(8865,9093),(8866,9094),(8867,9095),(8868,9096),(8869,9097),(8870,9098),(8871,9099),(8872,9100),(8873,9101),(8874,9102),(8875,9103),(8876,9104),(8877,9105),(8878,9106),(8879,9107),(8880,9108),(8881,9109),(8882,9110),(8883,9111),(8884,9112),(8885,9113),(8886,9114),(8887,9115),(8888,9116),(8889,9117),(8890,9118),(8891,9119),(8892,9120),(8893,9121),(8894,9122),(8895,9123),(8896,9124),(8897,9125),(8898,9126),(8899,9127),(8900,9128),(8901,9129),(8902,9130),(8903,9131),(8904,9132),(8905,9133),(8906,9134),(8907,9135),(8908,9136),(8909,9137),(8910,9138),(8911,9139),(8912,9140),(8913,9141),(8914,9142),(8915,9143),(8916,9144),(8917,9145),(8918,9146),(8919,9147),(8920,9148),(8921,9149),(8922,9150),(8923,9151),(8924,9152),(8925,9153),(8926,9154),(8927,9155),(8928,9156),(8929,9157),(8930,9158),(8931,9159),(8932,9160),(8933,9161),(8934,9162),(8935,9163),(8936,9164),(8937,9165),(8938,9166),(8939,9167),(8940,9168),(8941,9169),(8942,9170),(8943,9171),(8944,9172),(8945,9173),(8946,9174),(8947,9175),(8948,9176),(8949,9177),(8950,9178),(8951,9179),(8952,9180),(8953,9181),(8954,9182),(8955,9183),(8956,9184),(8957,9185),(8958,9186),(8959,9187)]
theorem count : slots.length=127 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0034

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0034.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0034.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0034.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0034.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0034.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0034.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0034.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0034.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0034.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0034.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0034.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0034.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0034.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0034.sound
