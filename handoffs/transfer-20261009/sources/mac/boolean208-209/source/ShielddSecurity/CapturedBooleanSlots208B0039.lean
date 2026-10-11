import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0039
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(9984,10209),(9985,10210),(9986,10211),(9987,10212),(9988,10213),(9989,10214),(9990,10215),(9991,10216),(9992,10217),(9993,10218),(9994,10219),(9995,10220),(9996,10221),(9997,10222),(9998,10223),(9999,10224),(10000,10225),(10001,10226),(10002,10227),(10003,10228),(10004,10229),(10005,10230),(10006,10231),(10007,10232),(10008,10233),(10009,10234),(10010,10235),(10011,10236),(10012,10237),(10013,10238),(10014,10239),(10015,10240),(10016,10241),(10017,10242),(10018,10243),(10019,10244),(10020,10245),(10021,10246),(10022,10247),(10023,10248),(10024,10249),(10025,10250),(10026,10251),(10027,10252),(10028,10253),(10029,10254),(10030,10255),(10031,10256),(10032,10257),(10033,10258),(10034,10259),(10035,10260),(10036,10261),(10037,10262),(10038,10263),(10039,10264),(10040,10265),(10041,10266),(10042,10267),(10043,10268),(10044,10269),(10045,10270),(10046,10271),(10047,10272),(10048,10273),(10049,10274),(10050,10275),(10051,10276),(10052,10277),(10053,10278),(10054,10279),(10055,10280),(10056,10281),(10057,10282),(10058,10283),(10059,10284),(10060,10285),(10061,10286),(10062,10287),(10063,10288),(10064,10289),(10065,10290),(10066,10291),(10067,10292),(10068,10293),(10069,10294),(10070,10295),(10071,10296),(10072,10297),(10073,10298),(10074,10299),(10075,10300),(10076,10301),(10077,10302),(10078,10303),(10079,10304),(10080,10305),(10081,10306),(10082,10307),(10083,10308),(10084,10309),(10085,10310),(10086,10311),(10087,10312),(10088,10313),(10089,10314),(10090,10315),(10091,10316),(10092,10317),(10093,10318),(10094,10319),(10095,10320),(10096,10321),(10097,10322),(10098,10323),(10099,10324),(10100,10325),(10101,10326),(10102,10327),(10103,10328),(10104,10329),(10105,10330),(10106,10331),(10107,10332),(10108,10333),(10109,10334),(10110,10335)]
theorem count : slots.length=127 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0039

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0039.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0039.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0039.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0039.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0039.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0039.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0039.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0039.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0039.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0039.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0039.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0039.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0039.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0039.sound
