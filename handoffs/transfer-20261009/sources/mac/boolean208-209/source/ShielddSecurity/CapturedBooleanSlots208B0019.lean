import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0019
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(4864,5010),(4865,5011),(4866,5012),(4867,5013),(4868,5014),(4869,5015),(4870,5016),(4871,5017),(4872,5018),(4873,5019),(4874,5020),(4875,5021),(4876,5022),(4877,5023),(4878,5024),(4879,5025),(4880,5026),(4881,5027),(4882,5028),(4883,5029),(4884,5030),(4885,5031),(4886,5032),(4887,5033),(4888,5034),(4889,5035),(4890,5036),(4891,5037),(4892,5038),(4893,5039),(4894,5040),(4895,5041),(4896,5042),(4897,5043),(4898,5044),(4899,5045),(4900,5046),(4901,5047),(4902,5048),(4903,5049),(4904,5050),(4905,5051),(4906,5052),(4907,5053),(4908,5054),(4909,5055),(4910,5056),(4911,5057),(4912,5058),(4913,5059),(4914,5060),(4915,5061),(4916,5062),(4917,5063),(4918,5064),(4919,5065),(4920,5066),(4921,5067),(4922,5068),(4923,5069),(4924,5070),(4925,5071),(4926,5072),(4927,5073),(4928,5074),(4929,5075),(4930,5076),(4931,5077),(4932,5078),(4933,5079),(4934,5080),(4935,5081),(4936,5082),(4937,5083),(4938,5084),(4939,5085),(4940,5086),(4941,5087),(4942,5088),(4943,5089),(4944,5090),(4945,5091),(4946,5092),(4947,5093),(4948,5094),(4949,5095),(4950,5096),(4951,5097),(4952,5098),(4953,5099),(4954,5100),(4955,5101),(4956,5102),(4957,5103),(4958,5104),(4959,5105),(4960,5106),(4961,5107),(4962,5108),(4963,5109),(4964,5110),(4965,5111),(4966,5112),(4967,5113),(4968,5114),(4969,5115),(4970,5116),(4971,5117),(4972,5118),(4973,5119),(4974,5120),(4975,5121),(4976,5122),(4977,5123),(4978,5124),(4979,5125),(4980,5126),(4981,5127),(4982,5128),(4983,5129),(4984,5130),(4985,5131),(4986,5132),(4987,5133),(4988,5134),(4989,5135),(4990,5136),(4991,5137),(4992,5138),(4993,5139),(4994,5140),(4995,5141),(4996,5142),(4997,5143),(4998,5144),(4999,5145),(5000,5146),(5001,5147),(5002,5148),(5003,5149),(5004,5150),(5005,5151),(5006,5152),(5007,5153),(5008,5154),(5009,5155),(5010,5156),(5011,5157),(5012,5158),(5013,5159),(5014,5160),(5015,5161),(5016,5162),(5017,5163),(5018,5164),(5019,5165),(5020,5166),(5021,5167),(5022,5168),(5023,5169),(5024,5170),(5025,5171),(5026,5172),(5027,5173),(5028,5174),(5029,5175),(5030,5176),(5031,5177),(5032,5178),(5033,5179),(5034,5180),(5035,5181),(5036,5182)]
theorem count : slots.length=173 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0019

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0019.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0019.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0019.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0019.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0019.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0019.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0019.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0019.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0019.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0019.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0019.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0019.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0019.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0019.sound
