import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0017
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(4352,4345),(4353,4346),(4354,4347),(4355,4348),(4356,4349),(4357,4350),(4358,4351),(4359,4352),(4360,4353),(4361,4354),(4362,4355),(4363,4356),(4364,4357),(4365,4358),(4366,4359),(4367,4360),(4368,4361),(4369,4362),(4370,4363),(4371,4364),(4372,4365),(4373,4366),(4374,4367),(4375,4368),(4376,4369),(4377,4370),(4378,4371),(4379,4372),(4380,4373),(4381,4374),(4382,4375),(4383,4376),(4384,4377),(4385,4378),(4386,4379),(4387,4380),(4388,4381),(4389,4382),(4390,4383),(4391,4384),(4392,4385),(4393,4386),(4394,4387),(4395,4388),(4396,4389),(4397,4390),(4398,4391),(4399,4392),(4400,4393),(4401,4394),(4402,4395),(4403,4396),(4404,4397),(4405,4398),(4406,4399),(4407,4400),(4408,4401),(4409,4402),(4410,4403),(4411,4404),(4412,4405),(4413,4406),(4414,4407),(4415,4408),(4416,4409),(4417,4410),(4419,4484),(4420,4485),(4421,4486),(4422,4487),(4423,4488),(4424,4489),(4425,4490),(4426,4491),(4427,4492),(4428,4493),(4429,4494),(4430,4495),(4431,4496),(4432,4497),(4433,4498),(4434,4499),(4435,4500),(4436,4501),(4437,4502),(4438,4503),(4439,4504),(4440,4505),(4441,4506),(4442,4507),(4443,4508),(4444,4509),(4445,4510),(4446,4511),(4447,4512),(4448,4513),(4449,4514),(4450,4515),(4451,4516),(4452,4517),(4453,4518),(4454,4519),(4455,4520),(4456,4521),(4457,4522),(4458,4523),(4459,4524),(4460,4525),(4461,4526),(4462,4527),(4463,4528),(4464,4529),(4465,4530),(4466,4531),(4471,4536),(4472,4537),(4473,4538),(4474,4539),(4475,4540),(4476,4541),(4477,4542),(4478,4543),(4479,4544),(4480,4545),(4481,4546),(4482,4547),(4483,4548),(4484,4549),(4485,4550),(4486,4551),(4487,4552),(4488,4553),(4489,4554),(4490,4555),(4491,4556),(4492,4557),(4493,4558),(4494,4559),(4495,4560),(4496,4561),(4497,4562),(4498,4563),(4499,4564),(4500,4565),(4501,4566),(4502,4567),(4503,4568),(4504,4569),(4505,4570),(4506,4571),(4507,4572),(4508,4573),(4509,4574),(4510,4575),(4511,4576),(4512,4577),(4513,4578),(4514,4579),(4515,4580),(4516,4581),(4517,4582),(4518,4583),(4519,4584),(4520,4585),(4521,4586),(4522,4587),(4523,4588),(4524,4589),(4525,4590),(4526,4591),(4527,4592),(4528,4593),(4529,4594),(4530,4595),(4531,4596),(4532,4597),(4533,4598),(4534,4599),(4535,4600),(4536,4601),(4537,4602),(4538,4603),(4539,4604),(4540,4605),(4541,4606),(4542,4607),(4543,4608),(4544,4609),(4545,4610),(4546,4611),(4547,4612),(4548,4613),(4549,4614),(4550,4615),(4551,4616),(4552,4617),(4553,4618),(4554,4619),(4555,4620),(4556,4621),(4557,4622),(4558,4623),(4559,4624),(4560,4625),(4561,4626),(4562,4627),(4563,4628),(4564,4629),(4565,4630),(4566,4631),(4567,4632),(4568,4633),(4569,4634),(4570,4635),(4571,4636),(4572,4637),(4573,4638),(4574,4639),(4575,4640),(4576,4641),(4577,4642),(4578,4643),(4579,4644),(4580,4645),(4581,4646),(4582,4647),(4583,4648),(4584,4649),(4585,4650),(4586,4651),(4587,4652),(4588,4653),(4589,4654),(4590,4655),(4591,4656),(4592,4657),(4593,4658),(4594,4659),(4595,4660),(4596,4661),(4597,4662),(4598,4663),(4600,4737),(4601,4738),(4602,4739),(4603,4740),(4604,4741),(4605,4742),(4606,4743),(4607,4744)]
theorem count : slots.length=250 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0017

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0017.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0017.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0017.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0017.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0017.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0017.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0017.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0017.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0017.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0017.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0017.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0017.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0017.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0017.sound
