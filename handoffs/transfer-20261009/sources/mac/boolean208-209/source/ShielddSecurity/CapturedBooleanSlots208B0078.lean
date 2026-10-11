import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0078
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(19968,19984),(19969,19985),(19970,19986),(19971,19987),(19972,19988),(19973,19989),(19974,19990),(19975,19991),(19976,19992),(19977,19993),(19978,19994),(19979,19995),(19980,19996),(19981,19997),(19982,19998),(19983,19999),(19984,20000),(19985,20001),(19986,20002),(19987,20003),(19988,20004),(19989,20005),(19990,20006),(19991,20007),(19992,20008),(19993,20009),(19994,20010),(19995,20011),(19996,20012),(19997,20013),(19998,20014),(19999,20015),(20000,20016),(20001,20017),(20002,20018),(20003,20019),(20004,20020),(20005,20021),(20006,20022),(20007,20023),(20008,20024),(20009,20025),(20010,20026),(20011,20027),(20012,20028),(20013,20029),(20014,20030),(20015,20031),(20016,20032),(20017,20033),(20018,20034),(20019,20035),(20020,20036),(20021,20037),(20022,20038),(20023,20039),(20024,20040),(20025,20041),(20026,20042),(20027,20043),(20028,20044),(20029,20045),(20030,20046),(20031,20047),(20032,20048),(20033,20049),(20034,20050),(20035,20051),(20036,20052),(20037,20053),(20038,20054),(20039,20055),(20040,20056),(20041,20057),(20042,20058),(20043,20059),(20044,20060),(20045,20061),(20046,20062),(20047,20063),(20048,20064),(20049,20065),(20050,20066),(20051,20067),(20052,20068),(20053,20069),(20054,20070),(20055,20071),(20056,20072),(20057,20073),(20058,20074),(20059,20075),(20060,20076),(20061,20077),(20062,20078),(20063,20079),(20064,20080),(20065,20081),(20066,20082),(20067,20083),(20068,20084),(20069,20085),(20070,20086),(20071,20087),(20072,20088),(20073,20089),(20074,20090),(20075,20091),(20076,20092),(20077,20093),(20078,20094),(20079,20095),(20080,20096),(20081,20097),(20082,20098),(20083,20099),(20084,20100),(20085,20101),(20086,20102),(20087,20103),(20088,20104),(20089,20105),(20090,20106),(20091,20107),(20092,20108),(20093,20109),(20094,20110),(20095,20111),(20096,20112),(20097,20113),(20098,20114),(20099,20115),(20100,20116),(20101,20117),(20102,20118),(20103,20119),(20104,20120),(20105,20121),(20106,20122),(20107,20123),(20108,20124),(20109,20125),(20110,20126),(20111,20127),(20112,20128),(20113,20129),(20114,20130),(20115,20131),(20116,20132),(20117,20133),(20118,20134),(20119,20135),(20120,20136),(20124,20137),(20125,20138),(20126,20139),(20127,20140),(20128,20141),(20129,20142),(20130,20143),(20131,20144),(20132,20145),(20133,20146),(20134,20147),(20135,20148),(20136,20149),(20137,20150),(20138,20151),(20139,20152),(20140,20153),(20141,20154),(20142,20155),(20143,20156),(20144,20157),(20145,20158),(20146,20159),(20147,20160),(20148,20161),(20149,20162),(20150,20163),(20151,20164),(20152,20165),(20153,20166),(20154,20167),(20155,20168),(20156,20169),(20157,20170),(20158,20171),(20159,20172),(20160,20173),(20161,20174),(20162,20175),(20163,20176),(20164,20177),(20165,20178),(20166,20179),(20167,20180),(20168,20181),(20169,20182),(20170,20183),(20171,20184),(20172,20185),(20173,20186),(20174,20187),(20175,20188),(20176,20189),(20177,20190),(20178,20191),(20179,20192),(20180,20193),(20181,20194),(20182,20195),(20183,20196),(20184,20197),(20185,20198),(20186,20199),(20187,20200),(20188,20201),(20189,20202),(20190,20203),(20191,20204),(20192,20205),(20193,20206),(20194,20207),(20195,20208),(20196,20209),(20197,20210),(20198,20211),(20199,20212),(20200,20213),(20201,20214),(20202,20215),(20203,20216),(20204,20217),(20205,20218),(20206,20219),(20207,20220),(20208,20221),(20209,20222),(20210,20223),(20211,20224),(20212,20225),(20213,20226),(20214,20227),(20215,20228),(20216,20229),(20217,20230),(20218,20231),(20219,20232),(20220,20233),(20221,20234),(20222,20235),(20223,20236)]
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
end ShielddSecurity.CapturedBooleanSlots208B0078

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0078.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0078.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0078.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0078.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0078.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0078.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0078.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0078.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0078.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0078.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0078.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0078.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0078.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0078.sound
