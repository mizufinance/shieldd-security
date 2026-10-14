-- GENERATED from table.json by generate.py. Do not hand edit.
import ShielddSecurity.BalanceBlindingSelectors672B024
import ShielddSecurity.BalanceBlindingSelectors672B025
import ShielddSecurity.BalanceBlindingSelectors672B026
import ShielddSecurity.BalanceBlindingSelectors672B027
import ShielddSecurity.BalanceBlindingSelectors672B028
import ShielddSecurity.BalanceBlindingSelectors672B029
import ShielddSecurity.BalanceBlindingSelectors672B030
import ShielddSecurity.BalanceBlindingSelectors672B031
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingSelectors672G03
open Compiler CompilerArithmeticTransport41 FixedSelectorAdapter480 ConcreteJubjubField01
noncomputable def tables : List (Entry × Group.Point F) := BalanceBlindingSelectors672B024.tables++BalanceBlindingSelectors672B025.tables++BalanceBlindingSelectors672B026.tables++BalanceBlindingSelectors672B027.tables++BalanceBlindingSelectors672B028.tables++BalanceBlindingSelectors672B029.tables++BalanceBlindingSelectors672B030.tables++BalanceBlindingSelectors672B031.tables
noncomputable def entries : List Entry := BalanceBlindingSelectors672B024.entries++BalanceBlindingSelectors672B025.entries++BalanceBlindingSelectors672B026.entries++BalanceBlindingSelectors672B027.entries++BalanceBlindingSelectors672B028.entries++BalanceBlindingSelectors672B029.entries++BalanceBlindingSelectors672B030.entries++BalanceBlindingSelectors672B031.entries
theorem checked : entries.all check=true := by
  simp only [entries,List.all_append,BalanceBlindingSelectors672B024.checked,BalanceBlindingSelectors672B025.checked,BalanceBlindingSelectors672B026.checked,BalanceBlindingSelectors672B027.checked,BalanceBlindingSelectors672B028.checked,BalanceBlindingSelectors672B029.checked,BalanceBlindingSelectors672B030.checked,BalanceBlindingSelectors672B031.checked,Bool.true_and]
theorem geometry_checked : tables.all (fun item => decide (FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F) (base item.1) (twice item.1) (triple item.1) item.2))=true := by
  simp only [tables,List.all_append,BalanceBlindingSelectors672B024.geometry_checked,BalanceBlindingSelectors672B025.geometry_checked,BalanceBlindingSelectors672B026.geometry_checked,BalanceBlindingSelectors672B027.geometry_checked,BalanceBlindingSelectors672B028.geometry_checked,BalanceBlindingSelectors672B029.geometry_checked,BalanceBlindingSelectors672B030.geometry_checked,BalanceBlindingSelectors672B031.geometry_checked,Bool.true_and]
theorem count : entries.length=16 := by rfl

end ShielddSecurity.BalanceBlindingSelectors672G03

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G03.tables
#print axioms ShielddSecurity.BalanceBlindingSelectors672G03.tables

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G03.entries
#print axioms ShielddSecurity.BalanceBlindingSelectors672G03.entries

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G03.checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G03.checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G03.geometry_checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G03.geometry_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G03.count
#print axioms ShielddSecurity.BalanceBlindingSelectors672G03.count
