-- GENERATED from table.json by generate.py. Do not hand edit.
import ShielddSecurity.BalanceBlindingSelectors672B040
import ShielddSecurity.BalanceBlindingSelectors672B041
import ShielddSecurity.BalanceBlindingSelectors672B042
import ShielddSecurity.BalanceBlindingSelectors672B043
import ShielddSecurity.BalanceBlindingSelectors672B044
import ShielddSecurity.BalanceBlindingSelectors672B045
import ShielddSecurity.BalanceBlindingSelectors672B046
import ShielddSecurity.BalanceBlindingSelectors672B047
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingSelectors672G05
open Compiler CompilerArithmeticTransport41 FixedSelectorAdapter480 ConcreteJubjubField01
noncomputable def tables : List (Entry × Group.Point F) := BalanceBlindingSelectors672B040.tables++BalanceBlindingSelectors672B041.tables++BalanceBlindingSelectors672B042.tables++BalanceBlindingSelectors672B043.tables++BalanceBlindingSelectors672B044.tables++BalanceBlindingSelectors672B045.tables++BalanceBlindingSelectors672B046.tables++BalanceBlindingSelectors672B047.tables
noncomputable def entries : List Entry := BalanceBlindingSelectors672B040.entries++BalanceBlindingSelectors672B041.entries++BalanceBlindingSelectors672B042.entries++BalanceBlindingSelectors672B043.entries++BalanceBlindingSelectors672B044.entries++BalanceBlindingSelectors672B045.entries++BalanceBlindingSelectors672B046.entries++BalanceBlindingSelectors672B047.entries
theorem checked : entries.all check=true := by
  simp only [entries,List.all_append,BalanceBlindingSelectors672B040.checked,BalanceBlindingSelectors672B041.checked,BalanceBlindingSelectors672B042.checked,BalanceBlindingSelectors672B043.checked,BalanceBlindingSelectors672B044.checked,BalanceBlindingSelectors672B045.checked,BalanceBlindingSelectors672B046.checked,BalanceBlindingSelectors672B047.checked,Bool.true_and]
theorem geometry_checked : tables.all (fun item => decide (FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F) (base item.1) (twice item.1) (triple item.1) item.2))=true := by
  simp only [tables,List.all_append,BalanceBlindingSelectors672B040.geometry_checked,BalanceBlindingSelectors672B041.geometry_checked,BalanceBlindingSelectors672B042.geometry_checked,BalanceBlindingSelectors672B043.geometry_checked,BalanceBlindingSelectors672B044.geometry_checked,BalanceBlindingSelectors672B045.geometry_checked,BalanceBlindingSelectors672B046.geometry_checked,BalanceBlindingSelectors672B047.geometry_checked,Bool.true_and]
theorem count : entries.length=16 := by rfl

end ShielddSecurity.BalanceBlindingSelectors672G05

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G05.tables
#print axioms ShielddSecurity.BalanceBlindingSelectors672G05.tables

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G05.entries
#print axioms ShielddSecurity.BalanceBlindingSelectors672G05.entries

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G05.checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G05.checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G05.geometry_checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G05.geometry_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G05.count
#print axioms ShielddSecurity.BalanceBlindingSelectors672G05.count
