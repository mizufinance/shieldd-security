-- GENERATED from maintained exact capture; do not edit.
import ShielddSecurity.RoutingPrecisionCapture818B00
import ShielddSecurity.RoutingPrecisionCapture818B01
import ShielddSecurity.RoutingPrecisionCapture818B02
import ShielddSecurity.RoutingPrecisionCapture818B03
import ShielddSecurity.RoutingPrecisionCapture818B04
import ShielddSecurity.RoutingPrecisionCapture818B05
import ShielddSecurity.RoutingPrecisionCapture818B06
import ShielddSecurity.RoutingPrecisionCapture818B07
import ShielddSecurity.RoutingPrecisionCapture818B08
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingPrecisionCapture818
open RoutingPrecisionAdapter817 Compiler CompilerAssertionBlock51 ConcreteJubjubField01
noncomputable def entries : List Entry := RoutingPrecisionCapture818B00.entries++RoutingPrecisionCapture818B01.entries++RoutingPrecisionCapture818B02.entries++RoutingPrecisionCapture818B03.entries++RoutingPrecisionCapture818B04.entries++RoutingPrecisionCapture818B05.entries++RoutingPrecisionCapture818B06.entries++RoutingPrecisionCapture818B07.entries++RoutingPrecisionCapture818B08.entries
theorem checked : entries.all check=true := by
  simp only [entries,List.all_append,RoutingPrecisionCapture818B00.checked,RoutingPrecisionCapture818B01.checked,RoutingPrecisionCapture818B02.checked,RoutingPrecisionCapture818B03.checked,RoutingPrecisionCapture818B04.checked,RoutingPrecisionCapture818B05.checked,RoutingPrecisionCapture818B06.checked,RoutingPrecisionCapture818B07.checked,RoutingPrecisionCapture818B08.checked,Bool.and_true]
theorem count : entries.length=66 := by decide +kernel
theorem indices : entries.map Entry.slot=List.range 66 := by decide +kernel
noncomputable def entry (slot : Fin 66) : Entry := entries[slot.val]'(by rw [count];exact slot.isLt)
theorem entry_checked (slot : Fin 66) : check (entry slot)=true :=
  List.all_eq_true.mp checked _ (List.getElem_mem _)
theorem entry_slot (slot : Fin 66) : (entry slot).slot=slot.val := by
  have slots := congrArg (fun xs : List Nat => xs[slot.val]?) indices
  simpa only [List.getElem?_map,List.getElem?_eq_getElem (show slot.val<entries.length by rw [count];exact slot.isLt),
    List.getElem?_range slot.isLt,Option.map_some,Option.some.injEq,entry] using slots

theorem equations (rho : Nat → F) (one : rho CompilerArithmeticTransport41.copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (slot : Fin 66) :
    rho (inverseOutput slot.val)=(rho (inputColumn slot.val)-((slot.val%33:Nat):F))*rho (hintColumn slot.val) ∧
    rho (zeroOutput slot.val)=(rho (inputColumn slot.val)-((slot.val%33:Nat):F))*rho (flagColumn slot.val) := by
  have result := RoutingPrecisionAdapter817.equations (entry slot) (entry_checked slot) rho one arithmetic
  simpa only [entry_slot] using result

theorem rows (rho : Nat → F) (one : rho CompilerArithmeticTransport41.copy=1) (slot : Fin 66)
    (inverse : rho (inverseOutput slot.val)=1-rho (flagColumn slot.val)) (zero : rho (zeroOutput slot.val)=0) :
    RoutingPrecisionAdapter817.Rows rho slot.val := by
  have result := RoutingPrecisionAdapter817.rows (entry slot) (entry_checked slot) rho one
    (by simpa only [entry_slot] using inverse) (by simpa only [entry_slot] using zero)
  simpa only [entry_slot] using result
end ShielddSecurity.RoutingPrecisionCapture818

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionCapture818.checked
#print axioms ShielddSecurity.RoutingPrecisionCapture818.checked

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionCapture818.count
#print axioms ShielddSecurity.RoutingPrecisionCapture818.count

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionCapture818.indices
#print axioms ShielddSecurity.RoutingPrecisionCapture818.indices

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionCapture818.entry_checked
#print axioms ShielddSecurity.RoutingPrecisionCapture818.entry_checked

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionCapture818.entry_slot
#print axioms ShielddSecurity.RoutingPrecisionCapture818.entry_slot

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionCapture818.equations
#print axioms ShielddSecurity.RoutingPrecisionCapture818.equations

set_option pp.all true in
#check @ShielddSecurity.RoutingPrecisionCapture818.rows
#print axioms ShielddSecurity.RoutingPrecisionCapture818.rows
