import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0062
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(15953,16154),(15954,16155),(15955,16156),(15956,16157),(15957,16158),(15958,16159),(15959,16160),(15960,16161),(15961,16162),(15962,16163),(15963,16164),(15964,16165),(15965,16166),(15966,16167),(15967,16168),(15968,16169),(15969,16170),(15970,16171),(15971,16172),(15972,16173),(15973,16174),(15974,16175),(15975,16176),(15976,16177),(15977,16178),(15978,16179),(15979,16180),(15980,16181),(15981,16182),(15982,16183),(15983,16184),(15984,16185),(15985,16186),(15986,16187),(15987,16188),(15988,16189),(15989,16190),(15990,16191),(15991,16192),(15992,16193),(15993,16194),(15994,16195),(15995,16196),(15996,16197),(15997,16198),(15998,16199),(15999,16200),(16000,16201),(16001,16202),(16002,16203),(16003,16204),(16004,16205),(16005,16206),(16006,16207),(16007,16208),(16008,16209),(16009,16210),(16010,16211),(16011,16212),(16012,16213),(16013,16214),(16014,16215),(16015,16216),(16016,16217),(16017,16218),(16018,16219),(16019,16220),(16020,16221),(16021,16222),(16022,16223),(16023,16224),(16024,16225),(16025,16226),(16026,16227),(16027,16228),(16028,16229),(16029,16230),(16030,16231),(16031,16232),(16032,16233),(16033,16234),(16034,16235),(16035,16236),(16036,16237),(16037,16238),(16038,16239),(16039,16240),(16040,16241),(16041,16242),(16042,16243),(16043,16244),(16044,16245),(16045,16246),(16046,16247),(16047,16248),(16048,16249),(16049,16250),(16050,16251),(16051,16252),(16052,16253),(16053,16254),(16054,16255),(16055,16256),(16056,16257),(16057,16258),(16058,16259),(16059,16260),(16060,16261),(16061,16262),(16062,16263),(16063,16264),(16064,16265),(16065,16266),(16066,16267),(16067,16268),(16068,16269),(16069,16270),(16070,16271),(16071,16272),(16072,16273),(16073,16274),(16074,16275),(16075,16276),(16076,16277),(16077,16278),(16078,16279),(16079,16280),(16080,16281),(16081,16282),(16082,16283),(16083,16284),(16084,16285),(16085,16286),(16086,16287),(16087,16288),(16088,16289),(16089,16290),(16090,16291),(16091,16292),(16092,16293),(16093,16294),(16094,16295),(16095,16296),(16096,16297),(16097,16298),(16098,16299),(16099,16300),(16100,16301),(16101,16302),(16102,16303),(16103,16304),(16104,16305),(16105,16306),(16106,16307),(16107,16308),(16108,16309),(16109,16310),(16110,16311),(16111,16312),(16112,16313),(16113,16314),(16114,16315),(16115,16316),(16116,16317),(16117,16318),(16118,16319),(16119,16320),(16120,16321),(16121,16322),(16122,16323),(16123,16324),(16124,16325),(16125,16326),(16126,16327),(16127,16328)]
theorem count : slots.length=175 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0062

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0062.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0062.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0062.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0062.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0062.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0062.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0062.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0062.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0062.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0062.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0062.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0062.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0062.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0062.sound
