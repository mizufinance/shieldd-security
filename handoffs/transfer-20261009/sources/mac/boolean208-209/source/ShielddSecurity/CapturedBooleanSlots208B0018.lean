import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0018
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(4608,4745),(4609,4746),(4610,4747),(4611,4748),(4612,4749),(4613,4750),(4614,4751),(4615,4752),(4616,4753),(4617,4754),(4618,4755),(4619,4756),(4620,4757),(4621,4758),(4622,4759),(4623,4760),(4624,4761),(4625,4762),(4626,4763),(4627,4764),(4628,4765),(4629,4766),(4630,4767),(4631,4768),(4632,4769),(4633,4770),(4634,4771),(4635,4772),(4636,4773),(4637,4774),(4638,4775),(4639,4776),(4640,4777),(4641,4778),(4642,4779),(4643,4780),(4644,4781),(4645,4782),(4646,4783),(4647,4784),(4650,4786),(4654,4791),(4655,4792),(4656,4793),(4657,4794),(4658,4795),(4659,4796),(4660,4797),(4661,4798),(4662,4799),(4663,4800),(4664,4801),(4665,4802),(4666,4803),(4667,4804),(4668,4805),(4669,4806),(4670,4807),(4671,4808),(4672,4809),(4673,4810),(4674,4811),(4675,4812),(4676,4813),(4677,4814),(4678,4815),(4679,4816),(4680,4817),(4681,4818),(4682,4819),(4683,4820),(4684,4821),(4685,4822),(4686,4823),(4687,4824),(4688,4825),(4689,4826),(4690,4827),(4691,4828),(4692,4829),(4693,4830),(4694,4831),(4695,4832),(4696,4833),(4697,4834),(4698,4835),(4699,4836),(4700,4837),(4701,4838),(4702,4839),(4703,4840),(4704,4841),(4705,4842),(4706,4843),(4707,4844),(4708,4845),(4709,4846),(4710,4847),(4711,4848),(4712,4849),(4713,4850),(4714,4851),(4715,4852),(4716,4853),(4717,4854),(4718,4855),(4719,4856),(4720,4857),(4721,4858),(4722,4859),(4723,4860),(4724,4861),(4725,4862),(4726,4863),(4727,4864),(4728,4865),(4729,4866),(4730,4867),(4731,4868),(4732,4869),(4733,4870),(4734,4871),(4735,4872),(4736,4873),(4737,4874),(4738,4875),(4739,4876),(4740,4877),(4741,4878),(4742,4879),(4743,4880),(4744,4881),(4745,4882),(4746,4883),(4747,4884),(4748,4885),(4749,4886),(4750,4887),(4751,4888),(4752,4889),(4753,4890),(4754,4891),(4755,4892),(4756,4893),(4757,4894),(4758,4895),(4759,4896),(4760,4897),(4761,4898),(4762,4899),(4763,4900),(4764,4901),(4765,4902),(4766,4903),(4767,4904),(4768,4905),(4769,4906),(4770,4907),(4771,4908),(4772,4909),(4773,4910),(4774,4911),(4775,4912),(4776,4913),(4777,4914),(4778,4915),(4779,4916),(4780,4917),(4781,4918),(4785,4931),(4786,4932),(4787,4933),(4788,4934),(4789,4935),(4790,4936),(4791,4937),(4792,4938),(4793,4939),(4794,4940),(4795,4941),(4796,4942),(4797,4943),(4798,4944),(4799,4945),(4800,4946),(4801,4947),(4802,4948),(4803,4949),(4804,4950),(4805,4951),(4806,4952),(4807,4953),(4808,4954),(4809,4955),(4810,4956),(4811,4957),(4812,4958),(4813,4959),(4814,4960),(4815,4961),(4816,4962),(4817,4963),(4818,4964),(4819,4965),(4820,4966),(4821,4967),(4822,4968),(4823,4969),(4824,4970),(4825,4971),(4826,4972),(4827,4973),(4828,4974),(4829,4975),(4830,4976),(4831,4977),(4832,4978),(4833,4979),(4834,4980),(4835,4981),(4836,4982),(4837,4983),(4838,4984),(4839,4985),(4840,4986),(4841,4987),(4842,4988),(4843,4989),(4844,4990),(4845,4991),(4846,4992),(4847,4993),(4848,4994),(4849,4995),(4850,4996),(4851,4997),(4852,4998),(4853,4999),(4854,5000),(4855,5001),(4856,5002),(4857,5003),(4858,5004),(4859,5005),(4860,5006),(4861,5007),(4862,5008),(4863,5009)]
theorem count : slots.length=248 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0018

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0018.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0018.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0018.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0018.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0018.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0018.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0018.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0018.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0018.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0018.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0018.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0018.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0018.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0018.sound
