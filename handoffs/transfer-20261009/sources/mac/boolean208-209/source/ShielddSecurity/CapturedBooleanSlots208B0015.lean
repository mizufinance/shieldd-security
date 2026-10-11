import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0015
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(3840,3834),(3841,3835),(3842,3836),(3843,3837),(3844,3838),(3845,3839),(3846,3840),(3847,3841),(3848,3842),(3849,3843),(3850,3844),(3851,3845),(3852,3846),(3853,3847),(3854,3848),(3855,3849),(3856,3850),(3857,3851),(3858,3852),(3859,3853),(3860,3854),(3861,3855),(3862,3856),(3863,3857),(3864,3858),(3865,3859),(3866,3860),(3867,3861),(3868,3862),(3869,3863),(3870,3864),(3871,3865),(3872,3866),(3873,3867),(3874,3868),(3875,3869),(3876,3870),(3877,3871),(3878,3872),(3879,3873),(3880,3874),(3881,3875),(3882,3876),(3883,3877),(3884,3878),(3885,3879),(3886,3880),(3887,3881),(3888,3882),(3889,3883),(3890,3884),(3891,3885),(3892,3886),(3893,3887),(3894,3888),(3895,3889),(3896,3890),(3897,3891),(3898,3892),(3899,3893),(3900,3894),(3901,3895),(3902,3896),(3903,3897),(3904,3898),(3905,3899),(3906,3900),(3907,3901),(3908,3902),(3909,3903),(3910,3904),(3911,3905),(3912,3906),(3913,3907),(3914,3908),(3915,3909),(3916,3910),(3917,3911),(3918,3912),(3919,3913),(3920,3914),(3921,3915),(3922,3916),(3923,3917),(3924,3918),(3925,3919),(3926,3920),(3927,3921),(3928,3922),(3929,3923),(3930,3924),(3931,3925),(3932,3926),(3933,3927),(3934,3928),(3935,3929),(3936,3930),(3937,3931),(3938,3932),(3939,3933),(3940,3934),(3941,3935),(3942,3936),(3943,3937),(3944,3938),(3945,3939),(3946,3940),(3947,3941),(3948,3942),(3949,3943),(3950,3944),(3951,3945),(3952,3946),(3953,3947),(3954,3948),(3955,3949),(3956,3950),(3957,3951),(3958,3952),(3959,3953),(3960,3954),(3961,3955),(3962,3956),(3963,3957),(3964,3958),(3965,3959),(3966,3960),(3967,3961),(3968,3962),(3969,3963),(3970,3964),(3971,3965),(3972,3966),(3973,3967),(3974,3968),(3975,3969),(3976,3970),(3977,3971),(3978,3972),(3979,3973),(3980,3974),(3981,3975),(3982,3976),(3983,3977),(3984,3978),(3985,3979),(3986,3980),(3987,3981),(3988,3982),(3989,3983),(3990,3984),(3991,3985),(3992,3986),(3993,3987),(3994,3988),(3995,3989),(3996,3990),(3997,3991),(3998,3992),(3999,3993),(4000,3994),(4001,3995),(4002,3996),(4003,3997),(4004,3998),(4005,3999),(4006,4000),(4007,4001),(4008,4002),(4009,4003),(4010,4004),(4011,4005),(4012,4006),(4013,4007),(4014,4008),(4015,4009),(4016,4010),(4017,4011),(4018,4012),(4019,4013),(4020,4014),(4021,4015),(4022,4016),(4023,4017),(4024,4018)]
theorem count : slots.length=185 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0015

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0015.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0015.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0015.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0015.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0015.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0015.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0015.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0015.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0015.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0015.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0015.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0015.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0015.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0015.sound
