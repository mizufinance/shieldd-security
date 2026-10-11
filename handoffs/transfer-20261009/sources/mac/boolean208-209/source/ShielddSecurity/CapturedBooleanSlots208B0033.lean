import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0033
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(8448,8681),(8449,8682),(8450,8683),(8451,8684),(8452,8685),(8453,8686),(8454,8687),(8455,8688),(8456,8689),(8457,8690),(8458,8691),(8459,8692),(8460,8693),(8461,8694),(8462,8695),(8463,8696),(8464,8697),(8465,8698),(8466,8699),(8467,8700),(8468,8701),(8469,8702),(8470,8703),(8471,8704),(8472,8705),(8473,8706),(8474,8707),(8475,8708),(8476,8709),(8477,8710),(8478,8711),(8479,8712),(8480,8713),(8481,8714),(8482,8715),(8483,8716),(8484,8717),(8485,8718),(8486,8719),(8487,8720),(8488,8721),(8489,8722),(8490,8723),(8491,8724),(8492,8725),(8493,8726),(8494,8727),(8495,8728),(8496,8729),(8497,8730),(8498,8731),(8499,8732),(8500,8733),(8501,8734),(8502,8735),(8503,8736),(8504,8737),(8505,8738),(8506,8739),(8507,8740),(8508,8741),(8509,8742),(8510,8743),(8511,8744),(8512,8745),(8513,8746),(8514,8747),(8515,8748),(8516,8749),(8517,8750),(8518,8751),(8519,8752),(8520,8753),(8521,8754),(8522,8755),(8523,8756),(8524,8757),(8525,8758),(8526,8759),(8527,8760),(8528,8761),(8529,8762),(8530,8763),(8531,8764),(8532,8765),(8533,8766),(8534,8767),(8535,8768),(8536,8769),(8537,8770),(8538,8771),(8539,8772),(8540,8773),(8541,8774),(8542,8775),(8543,8776),(8544,8777),(8545,8778),(8546,8779),(8547,8780),(8548,8781),(8549,8782),(8550,8783),(8551,8784),(8552,8785),(8553,8786),(8554,8787),(8555,8788),(8556,8789),(8557,8790),(8558,8791),(8559,8792),(8560,8793),(8561,8794),(8562,8795),(8563,8796),(8564,8797),(8565,8798),(8566,8799),(8567,8800),(8568,8801),(8569,8802),(8570,8803)]
theorem count : slots.length=123 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0033

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0033.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0033.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0033.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0033.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0033.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0033.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0033.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0033.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0033.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0033.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0033.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0033.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0033.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0033.sound
