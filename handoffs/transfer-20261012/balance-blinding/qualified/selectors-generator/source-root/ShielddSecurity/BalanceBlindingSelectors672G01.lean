-- GENERATED from table.json by generate.py. Do not hand edit.
import ShielddSecurity.BalanceBlindingSelectors672B008
import ShielddSecurity.BalanceBlindingSelectors672B009
import ShielddSecurity.BalanceBlindingSelectors672B010
import ShielddSecurity.BalanceBlindingSelectors672B011
import ShielddSecurity.BalanceBlindingSelectors672B012
import ShielddSecurity.BalanceBlindingSelectors672B013
import ShielddSecurity.BalanceBlindingSelectors672B014
import ShielddSecurity.BalanceBlindingSelectors672B015
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingSelectors672G01
open Compiler CompilerArithmeticTransport41 FixedSelectorAdapter480 ConcreteJubjubField01
noncomputable def tables : List (Entry × Group.Point F) := BalanceBlindingSelectors672B008.tables++BalanceBlindingSelectors672B009.tables++BalanceBlindingSelectors672B010.tables++BalanceBlindingSelectors672B011.tables++BalanceBlindingSelectors672B012.tables++BalanceBlindingSelectors672B013.tables++BalanceBlindingSelectors672B014.tables++BalanceBlindingSelectors672B015.tables
noncomputable def entries : List Entry := BalanceBlindingSelectors672B008.entries++BalanceBlindingSelectors672B009.entries++BalanceBlindingSelectors672B010.entries++BalanceBlindingSelectors672B011.entries++BalanceBlindingSelectors672B012.entries++BalanceBlindingSelectors672B013.entries++BalanceBlindingSelectors672B014.entries++BalanceBlindingSelectors672B015.entries
theorem checked : entries.all check=true := by
  simp only [entries,List.all_append,BalanceBlindingSelectors672B008.checked,BalanceBlindingSelectors672B009.checked,BalanceBlindingSelectors672B010.checked,BalanceBlindingSelectors672B011.checked,BalanceBlindingSelectors672B012.checked,BalanceBlindingSelectors672B013.checked,BalanceBlindingSelectors672B014.checked,BalanceBlindingSelectors672B015.checked,Bool.true_and]
theorem geometry_checked : tables.all (fun item => decide (FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F) (base item.1) (twice item.1) (triple item.1) item.2))=true := by
  simp only [tables,List.all_append,BalanceBlindingSelectors672B008.geometry_checked,BalanceBlindingSelectors672B009.geometry_checked,BalanceBlindingSelectors672B010.geometry_checked,BalanceBlindingSelectors672B011.geometry_checked,BalanceBlindingSelectors672B012.geometry_checked,BalanceBlindingSelectors672B013.geometry_checked,BalanceBlindingSelectors672B014.geometry_checked,BalanceBlindingSelectors672B015.geometry_checked,Bool.true_and]
theorem count : entries.length=16 := by rfl

end ShielddSecurity.BalanceBlindingSelectors672G01

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G01.tables
#print axioms ShielddSecurity.BalanceBlindingSelectors672G01.tables

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G01.entries
#print axioms ShielddSecurity.BalanceBlindingSelectors672G01.entries

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G01.checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G01.checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G01.geometry_checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G01.geometry_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G01.count
#print axioms ShielddSecurity.BalanceBlindingSelectors672G01.count
