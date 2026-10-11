import ShielddSecurity.CapturedArithmetic45B0000
import ShielddSecurity.CapturedAssertions50B0000
import ShielddSecurity.CompilerIndexed01
import ShielddSecurity.CompilerCoordinateZero69
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedRegisteredAudit70
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
noncomputable def arithmetic : List Row := (CapturedArithmetic45B0000.actual.drop 262).take 60
def productLeft (index : Nat) : Linear := ([[(35,1)],[(35,1)],[(0,-1),(36,1)],[(0,-1),(36,1)],[(115,1)],[(10,1)],[(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(35,1)],[(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(35,1)],[(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(36,1)],[(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(36,1)],[(119,1)],[(10,1)],[(35,1),(42,-1)],[(35,1),(42,-1)],[(36,1),(43,-1)],[(36,1),(43,-1)],[(123,1)],[(10,1)],[(42,1)],[(42,1)],[(0,-1),(43,1)],[(0,-1),(43,1)],[(127,1)],[(10,1)],[(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(42,1)],[(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(42,1)],[(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(43,1)],[(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(43,1)],[(131,1)],[(10,1)]]).getD index []
def productRight (index : Nat) : Linear := ([[(116,1)],[(115,1)],[(118,1)],[(117,1)],[(117,1)],[(23008,1)],[(120,1)],[(119,1)],[(122,1)],[(121,1)],[(121,1)],[(23020,1)],[(124,1)],[(123,1)],[(126,1)],[(125,1)],[(125,1)],[(23032,1)],[(128,1)],[(127,1)],[(130,1)],[(129,1)],[(129,1)],[(23044,1)],[(132,1)],[(131,1)],[(134,1)],[(133,1)],[(133,1)],[(23056,1)]]).getD index []
def zeroTerms (index : Nat) : Linear := ([[(35,1)],[(0,-1),(36,1)],[(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(35,1)],[(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(36,1)],[(35,1),(42,-1)],[(36,1),(43,-1)],[(42,1)],[(0,-1),(43,1)],[(0,2613035198500699080012737903016384954916552590968062488514021062113153911183),(42,1)],[(0,23326889571876200994796012627856472314977644248009733575144307806885254871463),(43,1)]]).getD index []
noncomputable def productCheck : Bool := (List.range 30).all (fun index =>
  CompilerIndexed01.checkUnoutlinedAt p copy arithmetic.toArray (2*index)
    ⟨subtract (productLeft index) (productRight index),[(23001+2*index,1)]⟩ &&
  CompilerIndexed01.checkUnoutlinedAt p copy arithmetic.toArray (2*index+1)
    ⟨productLeft index++productRight index,[(23001+2*index,1)]++scaleLinear 4 [(23000+2*index,1)]⟩)
theorem products_checked : productCheck=true := by decide +kernel
noncomputable def assertions : List Row := (CapturedAssertions50B0000.actual.drop 94).take 35
def recipes : List (Bool × Recipe) := [(true,.square [(115,1)] [(115,1)]),(true,.linear [(23000,1)] [(0,1),(115,-1)]),(true,.linear [] [(23002,1)]),(true,.square [(117,1)] [(117,1)]),(true,.linear [(23004,1)] [(0,1),(117,-1)]),(true,.linear [] [(23006,1)]),(true,.linear [] [(23010,1)]),(true,.square [(119,1)] [(119,1)]),(true,.linear [(23012,1)] [(0,1),(119,-1)]),(true,.linear [] [(23014,1)]),(true,.square [(121,1)] [(121,1)]),(true,.linear [(23016,1)] [(0,1),(121,-1)]),(true,.linear [] [(23018,1)]),(true,.linear [] [(23022,1)]),(true,.square [(123,1)] [(123,1)]),(true,.linear [(23024,1)] [(0,1),(123,-1)]),(true,.linear [] [(23026,1)]),(true,.square [(125,1)] [(125,1)]),(true,.linear [(23028,1)] [(0,1),(125,-1)]),(true,.linear [] [(23030,1)]),(true,.linear [] [(23034,1)]),(true,.square [(127,1)] [(127,1)]),(true,.linear [(23036,1)] [(0,1),(127,-1)]),(true,.linear [] [(23038,1)]),(true,.square [(129,1)] [(129,1)]),(true,.linear [(23040,1)] [(0,1),(129,-1)]),(true,.linear [] [(23042,1)]),(true,.linear [] [(23046,1)]),(true,.square [(131,1)] [(131,1)]),(true,.linear [(23048,1)] [(0,1),(131,-1)]),(true,.linear [] [(23050,1)]),(true,.square [(133,1)] [(133,1)]),(true,.linear [(23052,1)] [(0,1),(133,-1)]),(true,.linear [] [(23054,1)]),(true,.linear [] [(23058,1)])]
theorem assertions_checked : checkList p copy assertions recipes=true := by decide +kernel
noncomputable def block : Block p copy 35 := leaf p copy 35 assertions recipes (by decide +kernel) assertions_checked
variable {F : Type} [Field F]
def Primitive (rho : Nat → F) : Prop := ∀ index<10,
  CompilerZeroTest65.Primitive (eval rho (zeroTerms index)) (rho (115+2*index)) (rho (116+2*index))
variable [CharP F p]
theorem product_value (rho : Nat → F) (linked : rho copy=rho 0)
    (satisfied : Satisfies rho arithmetic) (index : Nat) (bound : index<30) :
    rho (23000+2*index)=eval rho (productLeft index)*eval rho (productRight index) := by
  have checks:=Bool.and_eq_true_iff.mp (List.all_eq_true.mp products_checked index (List.mem_range.mpr bound))
  have rows : Satisfies rho (unoutlineRows copy arithmetic) := by
    intro row member
    obtain ⟨original,included,rfl⟩:=List.mem_map.mp member
    simpa only [eval_unoutline rho copy _ linked] using satisfied original included
  have minus:=CompilerIndexed01.checkUnoutlinedAt_sound p copy arithmetic.toArray (2*index)
    ⟨subtract (productLeft index) (productRight index),[(23001+2*index,1)]⟩ checks.1
  have plus:=CompilerIndexed01.checkUnoutlinedAt_sound p copy arithmetic.toArray (2*index+1)
    ⟨productLeft index++productRight index,[(23001+2*index,1)]++scaleLinear 4 [(23000+2*index,1)]⟩ checks.2
  have h:=checked_product_sound rho (unoutlineRows copy arithmetic) (productLeft index) (productRight index)
    [(23000+2*index,1)] [(23001+2*index,1)] four_ne_zero rows
    (by simpa only [List.toList_toArray] using minus) (by simpa only [List.toList_toArray] using plus)
  simpa only [eval,Int.cast_one,one_mul,add_zero] using h

set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit70.arithmetic
#print axioms ShielddSecurity.CapturedRegisteredAudit70.arithmetic
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit70.productLeft
#print axioms ShielddSecurity.CapturedRegisteredAudit70.productLeft
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit70.productRight
#print axioms ShielddSecurity.CapturedRegisteredAudit70.productRight
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit70.zeroTerms
#print axioms ShielddSecurity.CapturedRegisteredAudit70.zeroTerms
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit70.productCheck
#print axioms ShielddSecurity.CapturedRegisteredAudit70.productCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit70.products_checked
#print axioms ShielddSecurity.CapturedRegisteredAudit70.products_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit70.assertions
#print axioms ShielddSecurity.CapturedRegisteredAudit70.assertions
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit70.recipes
#print axioms ShielddSecurity.CapturedRegisteredAudit70.recipes
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit70.assertions_checked
#print axioms ShielddSecurity.CapturedRegisteredAudit70.assertions_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit70.block
#print axioms ShielddSecurity.CapturedRegisteredAudit70.block
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit70.Primitive
#print axioms ShielddSecurity.CapturedRegisteredAudit70.Primitive
set_option pp.all true in
#check @ShielddSecurity.CapturedRegisteredAudit70.product_value
#print axioms ShielddSecurity.CapturedRegisteredAudit70.product_value
