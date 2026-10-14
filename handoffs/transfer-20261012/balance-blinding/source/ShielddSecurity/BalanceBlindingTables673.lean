import ShielddSecurity.BalanceBlindingSelectors672
import ShielddSecurity.BalanceBlindingDomain670
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingTables673
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 FixedSelectorAdapter480

noncomputable def first : Entry × Group.Point F := BalanceBlindingSelectors672B000.tables[0]

noncomputable def table (index : Nat) : Entry × Group.Point F :=
  (BalanceBlindingSelectors672.tables[index]?).getD first

theorem length : BalanceBlindingSelectors672.tables.length=126 := by rfl

theorem geometry (index : Nat) (bound : index<126) :
    FixedTableGeometry482.Equations (CapturedFirstSubgroup81.d:F)
      (base (table index).1) (twice (table index).1) (triple (table index).1) (table index).2 := by
  have before : index<BalanceBlindingSelectors672.tables.length := by rw [length];exact bound
  have checked := List.all_eq_true.mp BalanceBlindingSelectors672.geometry_checked
    (BalanceBlindingSelectors672.tables[index]) (List.getElem_mem before)
  simpa only [table,List.getElem?_eq_getElem before,Option.getD_some] using of_decide_eq_true checked

theorem indices_checked : (List.range 126).all (fun index => decide
    ((table index).1.low=22232+2*index ∧ (table index).1.high=22233+2*index))=true := by decide +kernel

theorem links_checked : (List.range 125).all (fun index => decide
    ((table index).2.x=(base (table (index+1)).1 : Group.Point F).x ∧
     (table index).2.y=(base (table (index+1)).1 : Group.Point F).y))=true := by decide +kernel

theorem linked (index : Nat) (bound : index<125) : (table index).2=base (table (index+1)).1 := by
  have parts := of_decide_eq_true (List.all_eq_true.mp links_checked index (List.mem_range.mpr bound))
  cases left : (table index).2 with
  | mk x y =>
    cases right : (base (table (index+1)).1 : Group.Point F) with
    | mk u v =>
      simp only [left,right] at parts
      exact congrArg₂ Group.Point.mk parts.1 parts.2

theorem base_coordinates (index : Nat) (bound : index<126) :
    base (table index).1=model.coordinates (4^index • BalanceBlindingDomain670.represented) := by
  induction index with
  | zero =>
    simp only [pow_zero,one_nsmul,BalanceBlindingDomain670.coordinates]
    rfl
  | succ index ih =>
    have previous := ih (by omega)
    have result := FixedTableGeometry482.coordinates (CapturedFirstSubgroup81.d:F) imaginary model
      (by rw [coefficient_eq];exact coefficient_no_unit_square) imaginary_square
      (4^index • BalanceBlindingDomain670.represented) (base (table index).1)
      (twice (table index).1) (triple (table index).1) (table index).2 previous.symm (geometry index (by omega))
    have next := (linked index (by omega)).symm.trans result.2.2
    have power : 4 • (4^index • BalanceBlindingDomain670.represented)=
        4^(index+1) • BalanceBlindingDomain670.represented := by
      rw [←mul_nsmul,Nat.mul_comm,pow_succ]
      rw [Nat.mul_comm]
    simpa only [power] using next

theorem table_coordinates (index : Nat) (bound : index<126) :
    twice (table index).1=model.coordinates (2 • (4^index • BalanceBlindingDomain670.represented)) ∧
    triple (table index).1=model.coordinates (3 • (4^index • BalanceBlindingDomain670.represented)) ∧
    (table index).2=model.coordinates (4 • (4^index • BalanceBlindingDomain670.represented)) :=
  FixedTableGeometry482.coordinates (CapturedFirstSubgroup81.d:F) imaginary model
    (by rw [coefficient_eq];exact coefficient_no_unit_square) imaginary_square
    (4^index • BalanceBlindingDomain670.represented) (base (table index).1)
    (twice (table index).1) (triple (table index).1) (table index).2
    (base_coordinates index bound).symm (geometry index bound)
end ShielddSecurity.BalanceBlindingTables673

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTables673.table
#print axioms ShielddSecurity.BalanceBlindingTables673.table

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTables673.length
#print axioms ShielddSecurity.BalanceBlindingTables673.length

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTables673.geometry
#print axioms ShielddSecurity.BalanceBlindingTables673.geometry

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTables673.indices_checked
#print axioms ShielddSecurity.BalanceBlindingTables673.indices_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTables673.links_checked
#print axioms ShielddSecurity.BalanceBlindingTables673.links_checked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTables673.linked
#print axioms ShielddSecurity.BalanceBlindingTables673.linked

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTables673.base_coordinates
#print axioms ShielddSecurity.BalanceBlindingTables673.base_coordinates

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingTables673.table_coordinates
#print axioms ShielddSecurity.BalanceBlindingTables673.table_coordinates
