import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0082
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(20996,20935),(20999,20938),(21000,20939),(21001,20940),(21002,20941),(21003,20942),(21004,20943),(21005,20944),(21006,20945),(21007,20946),(21008,20947),(21009,20948),(21010,20949),(21011,20950),(21012,20951),(21013,20952),(21014,20953),(21015,20954),(21016,20955),(21017,20956),(21018,20957),(21019,20958),(21020,20959),(21021,20960),(21022,20961),(21023,20962),(21024,20963),(21025,20964),(21026,20965),(21027,20966),(21028,20967),(21029,20968),(21030,20969),(21031,20970),(21032,20971),(21033,20972),(21034,20973),(21035,20974),(21036,20975),(21037,20976),(21038,20977),(21039,20978),(21040,20979),(21041,20980),(21042,20981),(21043,20982),(21044,20983),(21045,20984),(21046,20985),(21047,20986),(21048,20987),(21049,20988),(21050,20989),(21051,20990),(21052,20991),(21053,20992),(21054,20993),(21055,20994),(21056,20995),(21057,20996),(21058,20997),(21059,20998),(21060,20999),(21061,21000),(21062,21001),(21063,21002),(21064,21003),(21065,21004),(21066,21005),(21067,21006),(21068,21007),(21069,21008),(21070,21009),(21071,21010),(21072,21011),(21073,21012),(21074,21013),(21075,21014),(21076,21015),(21077,21016),(21078,21017),(21079,21018),(21080,21019),(21081,21020),(21082,21021),(21083,21022),(21084,21023),(21085,21024),(21086,21025),(21087,21026),(21088,21027),(21089,21028),(21090,21029),(21091,21030),(21092,21031),(21093,21032),(21094,21033),(21095,21034),(21096,21035),(21097,21036),(21098,21037),(21099,21038),(21100,21039),(21101,21040),(21102,21041),(21103,21042),(21104,21043),(21105,21044),(21106,21045),(21107,21046),(21108,21047),(21109,21048),(21110,21049),(21111,21050),(21112,21051),(21113,21052),(21114,21053),(21115,21054),(21116,21055),(21117,21056),(21118,21057),(21119,21058),(21120,21059),(21121,21060),(21122,21061),(21123,21062),(21124,21063),(21125,21064),(21126,21065),(21127,21066),(21128,21067),(21129,21068),(21130,21069),(21131,21070),(21132,21071),(21133,21072),(21134,21073),(21135,21074),(21136,21075),(21137,21076),(21138,21077),(21139,21078),(21140,21079),(21141,21080),(21142,21081),(21143,21082),(21144,21083),(21145,21084),(21146,21085),(21147,21086),(21148,21087),(21149,21088),(21150,21089),(21151,21090),(21152,21091),(21153,21092),(21154,21093),(21155,21094),(21156,21095),(21157,21096),(21158,21097),(21159,21098),(21160,21099),(21161,21100),(21162,21101),(21163,21102),(21164,21103),(21165,21104),(21166,21105),(21167,21106),(21168,21107),(21169,21108),(21170,21109),(21171,21110),(21172,21111),(21173,21112),(21174,21113),(21175,21114),(21176,21115),(21177,21116),(21178,21117),(21179,21118),(21180,21119),(21181,21120),(21182,21121),(21183,21122),(21184,21123),(21185,21124),(21186,21125),(21187,21126),(21188,21127),(21189,21128),(21190,21129),(21191,21130),(21192,21131),(21193,21132),(21194,21133),(21195,21134),(21196,21135),(21197,21136),(21198,21137),(21199,21138),(21200,21139),(21201,21140),(21202,21141),(21203,21142),(21204,21143),(21205,21144),(21206,21145),(21207,21146),(21208,21147),(21209,21148),(21210,21149),(21211,21150),(21212,21151),(21213,21152),(21214,21153),(21215,21154),(21216,21155),(21217,21156),(21218,21157),(21219,21158),(21220,21159),(21221,21160),(21222,21161),(21223,21162),(21224,21163),(21225,21164),(21226,21165),(21227,21166),(21228,21167),(21229,21168),(21230,21169),(21231,21170),(21232,21171),(21233,21172),(21234,21173),(21235,21174),(21236,21175),(21237,21176),(21238,21177),(21239,21178),(21240,21179),(21241,21180),(21242,21181),(21243,21182),(21244,21183),(21245,21184),(21246,21185),(21247,21186)]
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
end ShielddSecurity.CapturedBooleanSlots208B0082

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0082.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0082.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0082.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0082.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0082.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0082.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0082.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0082.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0082.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0082.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0082.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0082.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0082.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0082.sound
