-- GENERATED from table.json by generate.py. Do not hand edit.
import ShielddSecurity.BalanceBlindingSelectors672G00
import ShielddSecurity.BalanceBlindingSelectors672G01
import ShielddSecurity.BalanceBlindingSelectors672G02
import ShielddSecurity.BalanceBlindingSelectors672G03
import ShielddSecurity.BalanceBlindingSelectors672G04
import ShielddSecurity.BalanceBlindingSelectors672G05
import ShielddSecurity.BalanceBlindingSelectors672G06
import ShielddSecurity.BalanceBlindingSelectors672G07
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingSelectors672
open Compiler CompilerArithmeticTransport41 FixedSelectorAdapter480 ConcreteJubjubField01
noncomputable def tables : List (Entry × Group.Point F) := BalanceBlindingSelectors672G00.tables++BalanceBlindingSelectors672G01.tables++BalanceBlindingSelectors672G02.tables++BalanceBlindingSelectors672G03.tables++BalanceBlindingSelectors672G04.tables++BalanceBlindingSelectors672G05.tables++BalanceBlindingSelectors672G06.tables++BalanceBlindingSelectors672G07.tables
noncomputable def entries : List Entry := BalanceBlindingSelectors672G00.entries++BalanceBlindingSelectors672G01.entries++BalanceBlindingSelectors672G02.entries++BalanceBlindingSelectors672G03.entries++BalanceBlindingSelectors672G04.entries++BalanceBlindingSelectors672G05.entries++BalanceBlindingSelectors672G06.entries++BalanceBlindingSelectors672G07.entries
theorem checked : entries.all check=true := by
  simp only [entries,List.all_append,BalanceBlindingSelectors672G00.checked,BalanceBlindingSelectors672G01.checked,BalanceBlindingSelectors672G02.checked,BalanceBlindingSelectors672G03.checked,BalanceBlindingSelectors672G04.checked,BalanceBlindingSelectors672G05.checked,BalanceBlindingSelectors672G06.checked,BalanceBlindingSelectors672G07.checked,Bool.true_and]
theorem geometry_checked : tables.all (fun item => decide (FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F) (base item.1) (twice item.1) (triple item.1) item.2))=true := by
  simp only [tables,List.all_append,BalanceBlindingSelectors672G00.geometry_checked,BalanceBlindingSelectors672G01.geometry_checked,BalanceBlindingSelectors672G02.geometry_checked,BalanceBlindingSelectors672G03.geometry_checked,BalanceBlindingSelectors672G04.geometry_checked,BalanceBlindingSelectors672G05.geometry_checked,BalanceBlindingSelectors672G06.geometry_checked,BalanceBlindingSelectors672G07.geometry_checked,Bool.true_and]
theorem count : entries.length=126 := by
  simp only [entries,List.length_append,BalanceBlindingSelectors672G00.count,BalanceBlindingSelectors672G01.count,BalanceBlindingSelectors672G02.count,BalanceBlindingSelectors672G03.count,BalanceBlindingSelectors672G04.count,BalanceBlindingSelectors672G05.count,BalanceBlindingSelectors672G06.count,BalanceBlindingSelectors672G07.count]

end ShielddSecurity.BalanceBlindingSelectors672

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672.tables
#print axioms ShielddSecurity.BalanceBlindingSelectors672.tables

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672.entries
#print axioms ShielddSecurity.BalanceBlindingSelectors672.entries

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672.checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672.checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672.geometry_checked
#print axioms ShielddSecurity.BalanceBlindingSelectors672.geometry_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingSelectors672.count
#print axioms ShielddSecurity.BalanceBlindingSelectors672.count
