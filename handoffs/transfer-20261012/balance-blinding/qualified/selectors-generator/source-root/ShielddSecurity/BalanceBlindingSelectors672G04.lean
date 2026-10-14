-- GENERATED from table.json by generate.py. Do not hand edit.
import ShielddSecurity.BalanceBlindingSelectors672B032
import ShielddSecurity.BalanceBlindingSelectors672B033
import ShielddSecurity.BalanceBlindingSelectors672B034
import ShielddSecurity.BalanceBlindingSelectors672B035
import ShielddSecurity.BalanceBlindingSelectors672B036
import ShielddSecurity.BalanceBlindingSelectors672B037
import ShielddSecurity.BalanceBlindingSelectors672B038
import ShielddSecurity.BalanceBlindingSelectors672B039
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingSelectors672G04
open Compiler CompilerArithmeticTransport41 FixedSelectorAdapter480 ConcreteJubjubField01
noncomputable def tables : List (Entry × Group.Point F) := BalanceBlindingSelectors672B032.tables++BalanceBlindingSelectors672B033.tables++BalanceBlindingSelectors672B034.tables++BalanceBlindingSelectors672B035.tables++BalanceBlindingSelectors672B036.tables++BalanceBlindingSelectors672B037.tables++BalanceBlindingSelectors672B038.tables++BalanceBlindingSelectors672B039.tables
noncomputable def entries : List Entry := BalanceBlindingSelectors672B032.entries++BalanceBlindingSelectors672B033.entries++BalanceBlindingSelectors672B034.entries++BalanceBlindingSelectors672B035.entries++BalanceBlindingSelectors672B036.entries++BalanceBlindingSelectors672B037.entries++BalanceBlindingSelectors672B038.entries++BalanceBlindingSelectors672B039.entries
theorem checked : entries.all check=true := by
  simp only [entries,List.all_append,BalanceBlindingSelectors672B032.checked,BalanceBlindingSelectors672B033.checked,BalanceBlindingSelectors672B034.checked,BalanceBlindingSelectors672B035.checked,BalanceBlindingSelectors672B036.checked,BalanceBlindingSelectors672B037.checked,BalanceBlindingSelectors672B038.checked,BalanceBlindingSelectors672B039.checked,Bool.true_and]
theorem geometry_checked : tables.all (fun item => decide (FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F) (base item.1) (twice item.1) (triple item.1) item.2))=true := by
  simp only [tables,List.all_append,BalanceBlindingSelectors672B032.geometry_checked,BalanceBlindingSelectors672B033.geometry_checked,BalanceBlindingSelectors672B034.geometry_checked,BalanceBlindingSelectors672B035.geometry_checked,BalanceBlindingSelectors672B036.geometry_checked,BalanceBlindingSelectors672B037.geometry_checked,BalanceBlindingSelectors672B038.geometry_checked,BalanceBlindingSelectors672B039.geometry_checked,Bool.true_and]
theorem count : entries.length=16 := by rfl

end ShielddSecurity.BalanceBlindingSelectors672G04

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G04.tables
#print axioms ShielddSecurity.BalanceBlindingSelectors672G04.tables

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G04.entries
#print axioms ShielddSecurity.BalanceBlindingSelectors672G04.entries

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G04.checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G04.checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G04.geometry_checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G04.geometry_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G04.count
#print axioms ShielddSecurity.BalanceBlindingSelectors672G04.count
