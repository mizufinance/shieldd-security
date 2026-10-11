import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0070
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(17920,18102),(17921,18103),(17922,18104),(17923,18105),(17924,18106),(17925,18107),(17926,18108),(17927,18109),(17928,18110),(17929,18111),(17930,18112),(17931,18113),(17932,18114),(17933,18115),(17934,18116),(17935,18117),(17936,18118),(17937,18119),(17938,18120),(17939,18121),(17940,18122),(17941,18123),(17942,18124),(17943,18125),(17944,18126),(17945,18127),(17946,18128),(17947,18129),(17948,18130),(17949,18131),(17950,18132),(17951,18133),(17952,18134),(17953,18135),(17954,18136),(17955,18137),(17956,18138),(17957,18139),(17958,18140),(17959,18141),(17960,18142),(17961,18143),(17962,18144),(17963,18145),(17964,18146),(17965,18147),(17966,18148),(17967,18149),(17968,18150),(17969,18151),(17970,18152),(17971,18153),(17972,18154),(17973,18155),(17974,18156),(17975,18157),(17976,18158),(17977,18159),(17978,18160),(17979,18161),(17980,18162),(17981,18163),(17982,18164),(17983,18165),(17984,18166),(17985,18167),(17986,18168),(17987,18169),(17988,18170),(17989,18171),(17990,18172),(17991,18173),(17992,18174),(17993,18175),(17994,18176),(17995,18177),(17996,18178),(17997,18179),(18001,18180),(18002,18181),(18003,18182),(18004,18183),(18005,18184),(18006,18185),(18007,18186),(18008,18187),(18009,18188),(18010,18189),(18011,18190),(18012,18191),(18013,18192),(18014,18193),(18015,18194),(18016,18195),(18017,18196),(18018,18197),(18019,18198),(18020,18199),(18021,18200),(18022,18201),(18023,18202),(18024,18203),(18025,18204),(18026,18205),(18027,18206),(18028,18207),(18029,18208),(18030,18209),(18031,18210),(18032,18211),(18033,18212),(18034,18213),(18035,18214),(18036,18215),(18037,18216),(18038,18217),(18039,18218),(18040,18219),(18041,18220),(18042,18221),(18043,18222),(18044,18223),(18045,18224),(18046,18225),(18047,18226),(18048,18227),(18049,18228),(18050,18229),(18051,18230),(18052,18231),(18053,18232),(18054,18233),(18055,18234),(18056,18235),(18057,18236),(18058,18237),(18059,18238),(18060,18239),(18061,18240),(18062,18241),(18063,18242),(18064,18243),(18065,18244),(18066,18245),(18067,18246),(18068,18247),(18069,18248),(18070,18249),(18071,18250),(18072,18251),(18073,18252),(18074,18253),(18075,18254),(18076,18255),(18077,18256),(18078,18257),(18079,18258),(18080,18259),(18081,18260),(18082,18261),(18083,18262),(18084,18263),(18085,18264),(18086,18265),(18087,18266),(18088,18267),(18089,18268),(18090,18269),(18091,18270),(18092,18271),(18093,18272),(18094,18273),(18095,18274),(18096,18275),(18097,18276),(18098,18277),(18099,18278),(18100,18279),(18101,18280),(18102,18281),(18103,18282),(18104,18283),(18105,18284),(18106,18285),(18107,18286),(18108,18287),(18109,18288),(18110,18289),(18111,18290),(18112,18291),(18113,18292),(18114,18293),(18115,18294),(18116,18295),(18117,18296),(18118,18297),(18119,18298),(18120,18299),(18121,18300),(18122,18301),(18123,18302),(18124,18303),(18125,18304),(18126,18305),(18127,18306),(18128,18307),(18129,18308),(18130,18309),(18131,18310),(18132,18311),(18133,18312),(18134,18313),(18135,18314),(18136,18315),(18137,18316),(18138,18317),(18139,18318),(18140,18319),(18141,18320),(18142,18321),(18143,18322),(18144,18323),(18145,18324),(18146,18325),(18147,18326),(18148,18327),(18149,18328),(18150,18329),(18151,18330),(18152,18331),(18153,18332),(18154,18333),(18155,18334),(18156,18335),(18157,18336),(18158,18337),(18159,18338),(18160,18339),(18161,18340),(18162,18341),(18163,18342),(18164,18343),(18165,18344),(18166,18345),(18167,18346),(18168,18347),(18169,18348),(18170,18349),(18171,18350),(18172,18351),(18173,18352),(18174,18353),(18175,18354)]
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
end ShielddSecurity.CapturedBooleanSlots208B0070

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0070.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0070.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0070.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0070.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0070.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0070.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0070.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0070.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0070.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0070.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0070.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0070.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0070.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0070.sound
