-- GENERATED from table.json by generate.py. Do not hand edit.
import ShielddSecurity.BalanceBlindingSelectors672B016
import ShielddSecurity.BalanceBlindingSelectors672B017
import ShielddSecurity.BalanceBlindingSelectors672B018
import ShielddSecurity.BalanceBlindingSelectors672B019
import ShielddSecurity.BalanceBlindingSelectors672B020
import ShielddSecurity.BalanceBlindingSelectors672B021
import ShielddSecurity.BalanceBlindingSelectors672B022
import ShielddSecurity.BalanceBlindingSelectors672B023
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingSelectors672G02
open Compiler CompilerArithmeticTransport41 FixedSelectorAdapter480 ConcreteJubjubField01
noncomputable def tables : List (Entry × Group.Point F) := BalanceBlindingSelectors672B016.tables++BalanceBlindingSelectors672B017.tables++BalanceBlindingSelectors672B018.tables++BalanceBlindingSelectors672B019.tables++BalanceBlindingSelectors672B020.tables++BalanceBlindingSelectors672B021.tables++BalanceBlindingSelectors672B022.tables++BalanceBlindingSelectors672B023.tables
noncomputable def entries : List Entry := BalanceBlindingSelectors672B016.entries++BalanceBlindingSelectors672B017.entries++BalanceBlindingSelectors672B018.entries++BalanceBlindingSelectors672B019.entries++BalanceBlindingSelectors672B020.entries++BalanceBlindingSelectors672B021.entries++BalanceBlindingSelectors672B022.entries++BalanceBlindingSelectors672B023.entries
theorem checked : entries.all check=true := by
  simp only [entries,List.all_append,BalanceBlindingSelectors672B016.checked,BalanceBlindingSelectors672B017.checked,BalanceBlindingSelectors672B018.checked,BalanceBlindingSelectors672B019.checked,BalanceBlindingSelectors672B020.checked,BalanceBlindingSelectors672B021.checked,BalanceBlindingSelectors672B022.checked,BalanceBlindingSelectors672B023.checked,Bool.true_and]
theorem geometry_checked : tables.all (fun item => decide (FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F) (base item.1) (twice item.1) (triple item.1) item.2))=true := by
  simp only [tables,List.all_append,BalanceBlindingSelectors672B016.geometry_checked,BalanceBlindingSelectors672B017.geometry_checked,BalanceBlindingSelectors672B018.geometry_checked,BalanceBlindingSelectors672B019.geometry_checked,BalanceBlindingSelectors672B020.geometry_checked,BalanceBlindingSelectors672B021.geometry_checked,BalanceBlindingSelectors672B022.geometry_checked,BalanceBlindingSelectors672B023.geometry_checked,Bool.true_and]
theorem count : entries.length=16 := by rfl

end ShielddSecurity.BalanceBlindingSelectors672G02

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G02.tables
#print axioms ShielddSecurity.BalanceBlindingSelectors672G02.tables

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G02.entries
#print axioms ShielddSecurity.BalanceBlindingSelectors672G02.entries

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G02.checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G02.checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G02.geometry_checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G02.geometry_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G02.count
#print axioms ShielddSecurity.BalanceBlindingSelectors672G02.count
