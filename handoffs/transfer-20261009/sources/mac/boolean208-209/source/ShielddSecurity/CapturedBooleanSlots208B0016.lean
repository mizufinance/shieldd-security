import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0016
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(4290,4283),(4291,4284),(4292,4285),(4293,4286),(4294,4287),(4295,4288),(4296,4289),(4297,4290),(4298,4291),(4299,4292),(4300,4293),(4301,4294),(4302,4295),(4303,4296),(4304,4297),(4305,4298),(4306,4299),(4307,4300),(4308,4301),(4309,4302),(4310,4303),(4311,4304),(4312,4305),(4313,4306),(4314,4307),(4315,4308),(4316,4309),(4317,4310),(4318,4311),(4319,4312),(4320,4313),(4321,4314),(4322,4315),(4323,4316),(4324,4317),(4325,4318),(4326,4319),(4327,4320),(4328,4321),(4329,4322),(4330,4323),(4331,4324),(4332,4325),(4333,4326),(4334,4327),(4335,4328),(4336,4329),(4337,4330),(4338,4331),(4339,4332),(4340,4333),(4341,4334),(4342,4335),(4343,4336),(4344,4337),(4345,4338),(4346,4339),(4347,4340),(4348,4341),(4349,4342),(4350,4343),(4351,4344)]
theorem count : slots.length=62 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0016

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0016.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0016.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0016.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0016.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0016.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0016.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0016.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0016.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0016.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0016.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0016.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0016.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0016.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0016.sound
