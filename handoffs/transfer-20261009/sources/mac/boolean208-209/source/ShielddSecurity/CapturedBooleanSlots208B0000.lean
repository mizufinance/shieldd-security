import ShielddSecurity.BooleanHints207
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBooleanSlots208B0000
open BooleanHints207 CompilerAssertionBlock51 CompilerArithmeticTransport41
def slots : List (Nat × Nat) := [(0,10),(25,49),(26,50),(27,51),(28,52),(29,53),(30,54),(31,55),(32,56),(33,57),(34,58),(35,59),(36,60),(37,61),(38,62),(39,63),(40,64),(41,65),(42,66),(43,67),(44,68),(45,69),(46,70),(47,71),(48,72),(49,73),(50,74),(51,75),(52,76),(53,77),(54,78),(55,79),(56,80),(57,81),(58,82),(59,83),(60,84),(61,85),(62,86),(63,87),(64,88),(65,89),(66,90),(67,91),(68,92),(69,93),(70,94),(71,95),(72,96),(73,97),(74,98),(75,99),(76,100),(77,101),(78,102),(79,103),(80,104),(81,105),(82,106),(83,107),(84,108),(85,109),(86,110),(87,111),(88,112),(90,113),(94,115),(97,117),(101,119),(104,121),(108,123),(111,125),(115,127),(118,129),(122,131),(125,133),(129,184),(130,185),(131,186),(132,187),(133,188),(134,189),(135,190),(136,191),(137,192),(138,193),(139,194),(140,195),(141,196),(142,197),(143,198),(144,199),(145,200),(146,201),(147,202),(148,203),(149,204),(150,205),(151,206),(152,207),(153,208),(154,209),(155,210),(156,211),(157,212),(158,213),(159,214),(160,215),(165,216),(166,217),(167,218),(168,219),(169,220),(170,221),(171,222),(172,223),(173,224),(174,225),(175,226),(176,227),(177,228),(178,229),(179,230),(180,231),(181,232),(182,233),(183,234),(184,235),(185,236),(186,237),(187,238),(188,239),(189,240),(190,241),(191,242),(192,243),(193,244),(194,245),(195,246),(196,247),(197,248),(198,249),(199,250),(200,251),(201,252),(202,253),(203,254),(204,255),(205,256),(206,257),(207,258),(208,259),(209,260),(210,261),(211,262),(212,263),(213,264),(214,265),(215,266),(216,267),(217,268),(218,269),(219,270),(220,271),(221,272),(222,273),(223,274),(224,275),(225,276),(226,277),(227,278),(228,279),(229,280),(230,281),(231,282),(232,283),(233,284),(234,285),(235,286),(236,287),(237,288),(238,289),(239,290),(240,291),(241,292),(242,293),(243,294),(244,295),(245,296),(246,297),(247,298),(248,299),(249,300),(250,301),(251,302),(252,303),(253,304),(254,305),(255,306)]
theorem count : slots.length=199 := rfl
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
end ShielddSecurity.CapturedBooleanSlots208B0000

set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0000.slots
#print axioms ShielddSecurity.CapturedBooleanSlots208B0000.slots
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0000.count
#print axioms ShielddSecurity.CapturedBooleanSlots208B0000.count
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0000.checked
#print axioms ShielddSecurity.CapturedBooleanSlots208B0000.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0000.originals
#print axioms ShielddSecurity.CapturedBooleanSlots208B0000.originals
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0000.positions
#print axioms ShielddSecurity.CapturedBooleanSlots208B0000.positions
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0000.constructor
#print axioms ShielddSecurity.CapturedBooleanSlots208B0000.constructor
set_option pp.all true in
#check @ShielddSecurity.CapturedBooleanSlots208B0000.sound
#print axioms ShielddSecurity.CapturedBooleanSlots208B0000.sound
