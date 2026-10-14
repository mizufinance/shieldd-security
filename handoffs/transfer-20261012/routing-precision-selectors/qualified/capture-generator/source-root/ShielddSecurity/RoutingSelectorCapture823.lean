-- GENERATED from maintained exact capture; do not edit.
import ShielddSecurity.RoutingSelectorCapture823B00
import ShielddSecurity.RoutingSelectorCapture823B01
import ShielddSecurity.RoutingSelectorCapture823B02
import ShielddSecurity.RoutingSelectorCapture823B03
import ShielddSecurity.RoutingSelectorCapture823B04
import ShielddSecurity.RoutingSelectorCapture823B05
import ShielddSecurity.RoutingSelectorCapture823B06
import ShielddSecurity.RoutingSelectorCapture823B07
import ShielddSecurity.RoutingSelectorCapture823Sum0
import ShielddSecurity.RoutingSelectorCapture823Sum1
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RoutingSelectorCapture823
open RoutingSelectorAdapter822 Compiler CompilerAssertionBlock51 ConcreteJubjubField01
open RoutingSelectorAlgebra821 (suffix flags)
noncomputable def entries : List Entry := RoutingSelectorCapture823B00.entries++RoutingSelectorCapture823B01.entries++RoutingSelectorCapture823B02.entries++RoutingSelectorCapture823B03.entries++RoutingSelectorCapture823B04.entries++RoutingSelectorCapture823B05.entries++RoutingSelectorCapture823B06.entries++RoutingSelectorCapture823B07.entries
theorem checked : entries.all check=true := by
  simp only [entries,List.all_append,RoutingSelectorCapture823B00.checked,RoutingSelectorCapture823B01.checked,RoutingSelectorCapture823B02.checked,RoutingSelectorCapture823B03.checked,RoutingSelectorCapture823B04.checked,RoutingSelectorCapture823B05.checked,RoutingSelectorCapture823B06.checked,RoutingSelectorCapture823B07.checked,Bool.and_true]
theorem count : entries.length=32 := by decide +kernel
theorem indices : entries.map Entry.index=List.range 32 := by decide +kernel
noncomputable def entry (index : Fin 32) : Entry := entries[index.val]'(by rw [count];exact index.isLt)
theorem entry_checked (index : Fin 32) : check (entry index)=true :=
  List.all_eq_true.mp checked _ (List.getElem_mem _)
theorem entry_index (index : Fin 32) : (entry index).index=index.val := by
  have slots := congrArg (fun xs : List Nat => xs[index.val]?) indices
  simpa only [List.getElem?_map,List.getElem?_eq_getElem (show index.val<entries.length by rw [count];exact index.isLt),
    List.getElem?_range index.isLt,Option.map_some,Option.some.injEq,entry] using slots

theorem equations (rho : Nat → F) (one : rho CompilerArithmeticTransport41.copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) (index : Fin 32) :
    rho (orderOutput index.val)=eval rho (suffix 19457 index.val)*(1-eval rho (suffix 19523 index.val)) ∧
    rho (activeOutput index.val)=rho 10*(eval rho (suffix 19457 index.val)-eval rho (suffix 19523 index.val)) := by
  have result := RoutingSelectorAdapter822.equations (entry index) (entry_checked index) rho one arithmetic
  simpa only [entry_index] using result

theorem rows (rho : Nat → F) (index : Fin 32) (order : rho (orderOutput index.val)=0)
    (active : let value := eval rho (suffix 19523 index.val)+rho (activeOutput index.val);value*value=value) :
    RoutingSelectorAdapter822.Rows rho index.val := by
  have result := RoutingSelectorAdapter822.rows (entry index) (entry_checked index) rho
    (by simpa only [entry_index] using order) (by simpa only [entry_index] using active)
  simpa only [entry_index] using result
end ShielddSecurity.RoutingSelectorCapture823

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorCapture823.checked
#print axioms ShielddSecurity.RoutingSelectorCapture823.checked

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorCapture823.count
#print axioms ShielddSecurity.RoutingSelectorCapture823.count

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorCapture823.indices
#print axioms ShielddSecurity.RoutingSelectorCapture823.indices

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorCapture823.entry_checked
#print axioms ShielddSecurity.RoutingSelectorCapture823.entry_checked

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorCapture823.entry_index
#print axioms ShielddSecurity.RoutingSelectorCapture823.entry_index

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorCapture823.equations
#print axioms ShielddSecurity.RoutingSelectorCapture823.equations

set_option pp.all true in
#check @ShielddSecurity.RoutingSelectorCapture823.rows
#print axioms ShielddSecurity.RoutingSelectorCapture823.rows
