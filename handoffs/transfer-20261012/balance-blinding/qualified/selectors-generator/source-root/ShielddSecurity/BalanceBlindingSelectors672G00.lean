-- GENERATED from table.json by generate.py. Do not hand edit.
import ShielddSecurity.BalanceBlindingSelectors672B000
import ShielddSecurity.BalanceBlindingSelectors672B001
import ShielddSecurity.BalanceBlindingSelectors672B002
import ShielddSecurity.BalanceBlindingSelectors672B003
import ShielddSecurity.BalanceBlindingSelectors672B004
import ShielddSecurity.BalanceBlindingSelectors672B005
import ShielddSecurity.BalanceBlindingSelectors672B006
import ShielddSecurity.BalanceBlindingSelectors672B007
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingSelectors672G00
open Compiler CompilerArithmeticTransport41 FixedSelectorAdapter480 ConcreteJubjubField01
noncomputable def tables : List (Entry × Group.Point F) := BalanceBlindingSelectors672B000.tables++BalanceBlindingSelectors672B001.tables++BalanceBlindingSelectors672B002.tables++BalanceBlindingSelectors672B003.tables++BalanceBlindingSelectors672B004.tables++BalanceBlindingSelectors672B005.tables++BalanceBlindingSelectors672B006.tables++BalanceBlindingSelectors672B007.tables
noncomputable def entries : List Entry := BalanceBlindingSelectors672B000.entries++BalanceBlindingSelectors672B001.entries++BalanceBlindingSelectors672B002.entries++BalanceBlindingSelectors672B003.entries++BalanceBlindingSelectors672B004.entries++BalanceBlindingSelectors672B005.entries++BalanceBlindingSelectors672B006.entries++BalanceBlindingSelectors672B007.entries
theorem checked : entries.all check=true := by
  simp only [entries,List.all_append,BalanceBlindingSelectors672B000.checked,BalanceBlindingSelectors672B001.checked,BalanceBlindingSelectors672B002.checked,BalanceBlindingSelectors672B003.checked,BalanceBlindingSelectors672B004.checked,BalanceBlindingSelectors672B005.checked,BalanceBlindingSelectors672B006.checked,BalanceBlindingSelectors672B007.checked,Bool.true_and]
theorem geometry_checked : tables.all (fun item => decide (FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F) (base item.1) (twice item.1) (triple item.1) item.2))=true := by
  simp only [tables,List.all_append,BalanceBlindingSelectors672B000.geometry_checked,BalanceBlindingSelectors672B001.geometry_checked,BalanceBlindingSelectors672B002.geometry_checked,BalanceBlindingSelectors672B003.geometry_checked,BalanceBlindingSelectors672B004.geometry_checked,BalanceBlindingSelectors672B005.geometry_checked,BalanceBlindingSelectors672B006.geometry_checked,BalanceBlindingSelectors672B007.geometry_checked,Bool.true_and]
theorem count : entries.length=16 := by rfl

end ShielddSecurity.BalanceBlindingSelectors672G00

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G00.tables
#print axioms ShielddSecurity.BalanceBlindingSelectors672G00.tables

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G00.entries
#print axioms ShielddSecurity.BalanceBlindingSelectors672G00.entries

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G00.checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G00.checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G00.geometry_checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G00.geometry_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G00.count
#print axioms ShielddSecurity.BalanceBlindingSelectors672G00.count
