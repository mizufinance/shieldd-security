import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0014
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(3773,3767),(3774,3768),(3775,3769),(3776,3770),(3777,3771),(3778,3772),(3779,3773),(3780,3774),(3781,3775),(3782,3776),(3783,3777),(3784,3778),(3785,3779),(3786,3780),(3787,3781),(3788,3782),(3789,3783),(3790,3784),(3791,3785),(3792,3786),(3793,3787),(3794,3788),(3795,3789),(3796,3790),(3797,3791),(3798,3792),(3799,3793),(3800,3794),(3801,3795),(3802,3796),(3803,3797),(3804,3798),(3805,3799),(3806,3800),(3807,3801),(3808,3802),(3809,3803),(3810,3804),(3811,3805),(3812,3806),(3813,3807),(3814,3808),(3815,3809),(3816,3810),(3817,3811),(3818,3812),(3819,3813),(3820,3814),(3821,3815),(3822,3816),(3823,3817),(3824,3818),(3825,3819),(3826,3820),(3827,3821),(3828,3822),(3829,3823),(3830,3824),(3831,3825),(3832,3826),(3833,3827),(3834,3828),(3835,3829),(3836,3830),(3837,3831),(3838,3832),(3839,3833)]
theorem count : slots.length=67 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0014

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0014.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0014.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0014.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0014.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0014.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0014.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0014.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0014.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0014.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0014.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0014.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0014.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0014.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0014.sound
