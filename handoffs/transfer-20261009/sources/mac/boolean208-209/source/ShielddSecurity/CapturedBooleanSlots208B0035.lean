import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0035
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(8960,9188),(8961,9189),(8962,9190),(8963,9191),(8964,9192),(8965,9193),(8966,9194),(8967,9195),(8968,9196),(8969,9197),(8970,9198),(8971,9199),(8972,9200),(8973,9201),(8974,9202),(8975,9203),(8976,9204),(8977,9205),(8978,9206),(8979,9207),(8980,9208),(8981,9209),(8982,9210),(8983,9211),(8984,9212),(8985,9213),(8986,9214),(8987,9215),(8988,9216),(8989,9217),(8990,9218),(8991,9219),(8992,9220),(8993,9221),(8994,9222),(8995,9223),(8996,9224),(8997,9225),(8998,9226),(8999,9227),(9000,9228),(9001,9229),(9002,9230),(9003,9231),(9004,9232),(9005,9233),(9006,9234),(9007,9235),(9008,9236),(9009,9237),(9010,9238),(9011,9239),(9012,9240),(9013,9241),(9014,9242),(9015,9243),(9016,9244),(9017,9245),(9018,9246),(9019,9247),(9020,9248),(9021,9249),(9022,9250),(9023,9251),(9024,9252),(9025,9253),(9026,9254),(9027,9255),(9028,9256),(9029,9257),(9030,9258),(9031,9259),(9032,9260),(9033,9261),(9034,9262),(9035,9263),(9036,9264),(9037,9265),(9038,9266),(9039,9267),(9040,9268),(9041,9269),(9042,9270),(9043,9271),(9044,9272),(9045,9273),(9046,9274),(9047,9275),(9048,9276),(9049,9277),(9050,9278),(9051,9279),(9052,9280),(9053,9281),(9054,9282),(9055,9283),(9056,9284),(9057,9285),(9058,9286),(9059,9287),(9060,9288),(9061,9289),(9062,9290),(9063,9291),(9064,9292),(9065,9293),(9066,9294),(9067,9295),(9068,9296),(9069,9297),(9070,9298),(9071,9299),(9072,9300),(9073,9301),(9074,9302),(9075,9303),(9076,9304),(9077,9305),(9078,9306),(9079,9307),(9080,9308),(9081,9309),(9082,9310),(9083,9311),(9084,9312),(9085,9313),(9086,9314),(9087,9315),(9088,9316),(9093,9317)]
theorem count : slots.length=130 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0035

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0035.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0035.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0035.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0035.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0035.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0035.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0035.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0035.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0035.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0035.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0035.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0035.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0035.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0035.sound
