import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0002
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(512,560),(513,561),(514,562),(515,563),(516,564),(517,565),(518,566),(519,567),(520,568),(521,569),(522,570),(523,571),(524,572),(525,573),(526,574),(527,575),(528,576),(529,577),(530,578),(531,579),(532,580),(533,581),(534,582),(535,583),(536,584),(537,585),(538,586),(539,587),(540,588),(541,589),(542,590),(543,591),(544,592),(545,593),(546,594),(547,595),(548,596),(549,597),(550,598),(551,599),(552,600),(553,601),(554,602),(555,603),(556,604),(557,605),(558,606),(559,607),(560,608),(561,609),(562,610),(563,611),(564,612),(565,613),(566,614),(567,615),(568,616),(569,617),(570,618),(571,619),(572,620),(573,621),(574,622),(575,623),(576,624),(577,625),(578,626),(579,627),(580,628),(581,629),(582,630),(583,631),(584,632),(585,633),(586,634),(587,635),(588,636),(589,637),(590,638),(591,639),(592,640),(593,641),(594,642),(595,643),(596,644),(597,645),(598,646),(599,647),(600,648),(601,649),(602,650),(603,651),(604,652),(605,653),(606,654),(607,655),(608,656),(609,657),(610,658),(611,659),(612,660),(613,661),(614,662),(615,663),(616,664),(617,665),(618,666),(619,667),(620,668),(621,669),(622,670),(623,671),(624,672),(625,673),(626,674),(627,675),(628,676),(629,677),(630,678),(631,679),(632,680),(633,681),(634,682),(635,683),(636,684),(637,685),(638,686),(639,687),(640,688),(641,689),(642,690),(643,691),(644,692),(645,693),(646,694),(647,695),(648,696),(649,697),(650,698),(651,699),(652,700),(653,701),(654,702),(655,703),(656,704),(657,705),(658,706),(659,707),(660,708),(661,709),(662,710),(663,711),(664,712),(665,713),(666,714),(667,715),(668,716),(669,717),(670,718),(671,719),(672,720),(673,721),(674,722),(675,723),(676,724),(677,725),(681,726),(682,727),(683,728),(684,729),(685,730),(686,731),(687,732),(688,733),(689,734),(690,735),(691,736),(692,737),(693,738),(694,739),(695,740),(696,741),(697,742),(698,743),(699,744),(700,745),(701,746),(702,747),(703,748),(704,749),(705,750),(706,751),(707,752),(708,753),(709,754),(710,755),(711,756),(712,757),(713,758),(714,759),(715,760),(716,761),(717,762),(718,763),(719,764),(720,765),(721,766),(722,767),(723,768),(724,769),(725,770),(726,771),(727,772),(728,773),(729,774),(730,775),(731,776),(732,777),(733,778),(734,779),(735,780),(736,781),(737,782),(738,783),(739,784),(740,785),(741,786),(742,787),(743,788),(744,789),(745,790),(746,791),(747,792),(748,793),(749,794),(750,795),(751,796),(752,797),(753,798),(754,799),(755,800),(756,801),(757,802),(758,803),(759,804),(760,805),(761,806),(762,807),(763,808),(764,809),(765,810),(766,811),(767,812)]
theorem count : slots.length=253 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0002

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0002.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0002.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0002.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0002.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0002.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0002.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0002.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0002.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0002.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0002.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0002.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0002.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0002.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0002.sound
