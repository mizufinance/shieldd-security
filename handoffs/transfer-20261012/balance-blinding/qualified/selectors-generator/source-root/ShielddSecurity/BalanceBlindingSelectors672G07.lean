-- GENERATED from table.json by generate.py. Do not hand edit.
import ShielddSecurity.BalanceBlindingSelectors672B056
import ShielddSecurity.BalanceBlindingSelectors672B057
import ShielddSecurity.BalanceBlindingSelectors672B058
import ShielddSecurity.BalanceBlindingSelectors672B059
import ShielddSecurity.BalanceBlindingSelectors672B060
import ShielddSecurity.BalanceBlindingSelectors672B061
import ShielddSecurity.BalanceBlindingSelectors672B062
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingSelectors672G07
open Compiler CompilerArithmeticTransport41 FixedSelectorAdapter480 ConcreteJubjubField01
noncomputable def tables : List (Entry × Group.Point F) := BalanceBlindingSelectors672B056.tables++BalanceBlindingSelectors672B057.tables++BalanceBlindingSelectors672B058.tables++BalanceBlindingSelectors672B059.tables++BalanceBlindingSelectors672B060.tables++BalanceBlindingSelectors672B061.tables++BalanceBlindingSelectors672B062.tables
noncomputable def entries : List Entry := BalanceBlindingSelectors672B056.entries++BalanceBlindingSelectors672B057.entries++BalanceBlindingSelectors672B058.entries++BalanceBlindingSelectors672B059.entries++BalanceBlindingSelectors672B060.entries++BalanceBlindingSelectors672B061.entries++BalanceBlindingSelectors672B062.entries
theorem checked : entries.all check=true := by
  simp only [entries,List.all_append,BalanceBlindingSelectors672B056.checked,BalanceBlindingSelectors672B057.checked,BalanceBlindingSelectors672B058.checked,BalanceBlindingSelectors672B059.checked,BalanceBlindingSelectors672B060.checked,BalanceBlindingSelectors672B061.checked,BalanceBlindingSelectors672B062.checked,Bool.true_and]
theorem geometry_checked : tables.all (fun item => decide (FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F) (base item.1) (twice item.1) (triple item.1) item.2))=true := by
  simp only [tables,List.all_append,BalanceBlindingSelectors672B056.geometry_checked,BalanceBlindingSelectors672B057.geometry_checked,BalanceBlindingSelectors672B058.geometry_checked,BalanceBlindingSelectors672B059.geometry_checked,BalanceBlindingSelectors672B060.geometry_checked,BalanceBlindingSelectors672B061.geometry_checked,BalanceBlindingSelectors672B062.geometry_checked,Bool.true_and]
theorem count : entries.length=14 := by rfl

end ShielddSecurity.BalanceBlindingSelectors672G07

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G07.tables
#print axioms ShielddSecurity.BalanceBlindingSelectors672G07.tables

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G07.entries
#print axioms ShielddSecurity.BalanceBlindingSelectors672G07.entries

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G07.checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G07.checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G07.geometry_checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G07.geometry_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G07.count
#print axioms ShielddSecurity.BalanceBlindingSelectors672G07.count
