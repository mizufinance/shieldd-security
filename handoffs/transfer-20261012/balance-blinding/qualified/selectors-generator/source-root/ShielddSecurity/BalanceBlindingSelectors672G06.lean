-- GENERATED from table.json by generate.py. Do not hand edit.
import ShielddSecurity.BalanceBlindingSelectors672B048
import ShielddSecurity.BalanceBlindingSelectors672B049
import ShielddSecurity.BalanceBlindingSelectors672B050
import ShielddSecurity.BalanceBlindingSelectors672B051
import ShielddSecurity.BalanceBlindingSelectors672B052
import ShielddSecurity.BalanceBlindingSelectors672B053
import ShielddSecurity.BalanceBlindingSelectors672B054
import ShielddSecurity.BalanceBlindingSelectors672B055
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingSelectors672G06
open Compiler CompilerArithmeticTransport41 FixedSelectorAdapter480 ConcreteJubjubField01
noncomputable def tables : List (Entry × Group.Point F) := BalanceBlindingSelectors672B048.tables++BalanceBlindingSelectors672B049.tables++BalanceBlindingSelectors672B050.tables++BalanceBlindingSelectors672B051.tables++BalanceBlindingSelectors672B052.tables++BalanceBlindingSelectors672B053.tables++BalanceBlindingSelectors672B054.tables++BalanceBlindingSelectors672B055.tables
noncomputable def entries : List Entry := BalanceBlindingSelectors672B048.entries++BalanceBlindingSelectors672B049.entries++BalanceBlindingSelectors672B050.entries++BalanceBlindingSelectors672B051.entries++BalanceBlindingSelectors672B052.entries++BalanceBlindingSelectors672B053.entries++BalanceBlindingSelectors672B054.entries++BalanceBlindingSelectors672B055.entries
theorem checked : entries.all check=true := by
  simp only [entries,List.all_append,BalanceBlindingSelectors672B048.checked,BalanceBlindingSelectors672B049.checked,BalanceBlindingSelectors672B050.checked,BalanceBlindingSelectors672B051.checked,BalanceBlindingSelectors672B052.checked,BalanceBlindingSelectors672B053.checked,BalanceBlindingSelectors672B054.checked,BalanceBlindingSelectors672B055.checked,Bool.true_and]
theorem geometry_checked : tables.all (fun item => decide (FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F) (base item.1) (twice item.1) (triple item.1) item.2))=true := by
  simp only [tables,List.all_append,BalanceBlindingSelectors672B048.geometry_checked,BalanceBlindingSelectors672B049.geometry_checked,BalanceBlindingSelectors672B050.geometry_checked,BalanceBlindingSelectors672B051.geometry_checked,BalanceBlindingSelectors672B052.geometry_checked,BalanceBlindingSelectors672B053.geometry_checked,BalanceBlindingSelectors672B054.geometry_checked,BalanceBlindingSelectors672B055.geometry_checked,Bool.true_and]
theorem count : entries.length=16 := by rfl

end ShielddSecurity.BalanceBlindingSelectors672G06

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G06.tables
#print axioms ShielddSecurity.BalanceBlindingSelectors672G06.tables

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G06.entries
#print axioms ShielddSecurity.BalanceBlindingSelectors672G06.entries

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G06.checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G06.checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G06.geometry_checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672G06.geometry_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672G06.count
#print axioms ShielddSecurity.BalanceBlindingSelectors672G06.count
