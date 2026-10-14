import ShielddSecurity.BalanceBlindingTrace675
import ShielddSecurity.BalanceBlindingTables673
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.BalanceBlindingLocal676
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open BalanceBlindingTrace675 (trace window empty)

theorem trace_length (scalar : Nat) : (trace scalar).length=126 := by
  simp only [trace,FixedTraceConstruction478.windows,FixedTraceConstruction478.trace_length,
    VariableTraceBits446.pairs_length,encodeBits_length]

theorem window_equations (scalar index : Nat) (bound : index<126) :
    GroupFixedWindows.FixedWindowEquations (CapturedFirstSubgroup81.d:F)
      (FixedTraceAccess486.before (model.coordinates 0) (trace scalar) empty index)
      (model.coordinates (4^index • BalanceBlindingDomain670.represented)) (window scalar index) := by
  have equations := FixedTraceAccess486.indexed_equations (CapturedFirstSubgroup81.d:F)
    (model.coordinates BalanceBlindingDomain670.represented) (model.coordinates 0) (trace scalar) empty index
    (by rw [trace_length];exact bound)
    (FixedTraceConstruction478.trace_equations (CapturedFirstSubgroup81.d:F) imaginary model
      (by rw [coefficient_eq];exact coefficient_no_unit_square) imaginary_square
      BalanceBlindingDomain670.represented 0 (VariableTraceBits446.pairs (encodeBits 252 scalar)))
  have base := FixedTraceAccess486.constructed_base model BalanceBlindingDomain670.represented 0
    (VariableTraceBits446.pairs (encodeBits 252 scalar)) empty index
    (by rw [VariableTraceBits446.pairs_length,encodeBits_length];omega)
  change FixedTraceAccess486.beforeBase (model.coordinates BalanceBlindingDomain670.represented)
    (trace scalar) empty index = model.coordinates (4^index • BalanceBlindingDomain670.represented) at base
  rw [base] at equations
  exact equations

theorem add_equations (scalar index : Nat) (bound : index<126) :
    TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:F)
      (FixedTraceAccess486.before (model.coordinates 0) (trace scalar) empty index)
      (Group.windowPoint (if (window scalar index).low then 1 else 0) (if (window scalar index).high then 1 else 0)
        (FixedSelectorAdapter480.base (BalanceBlindingTables673.table index).1)
        (FixedSelectorAdapter480.twice (BalanceBlindingTables673.table index).1)
        (FixedSelectorAdapter480.triple (BalanceBlindingTables673.table index).1))
      (window scalar index).output := by
  have equations := window_equations scalar index bound
  have fromTrace := GroupFixedWindows.fixed_table_coordinates (CapturedFirstSubgroup81.d:F) imaginary model
    (by rw [coefficient_eq];exact coefficient_no_unit_square) imaginary_square
    (4^index • BalanceBlindingDomain670.represented) (window scalar index) equations.1
  have fromTable := BalanceBlindingTables673.table_coordinates index bound
  rw [BalanceBlindingTables673.base_coordinates index bound,fromTable.1,fromTable.2.1]
  have result := equations.2
  rw [fromTrace.1,fromTrace.2.1] at result
  exact result

theorem bits (scalar index : Nat) (bound : index<126) :
    ((window scalar index).low,(window scalar index).high)=
      ((encodeBits 252 scalar)[2*index]?.getD false,(encodeBits 252 scalar)[2*index+1]?.getD false) :=
  FixedTraceAccess486.windows_bits model BalanceBlindingDomain670.represented (encodeBits 252 scalar)
    (by simp) empty index bound

theorem before_positive (scalar index : Nat) (lower : 1 ≤ index) :
    FixedTraceAccess486.before (model.coordinates 0) (trace scalar) empty index=(window scalar (index-1)).output := by
  cases index with
  | zero => omega
  | succ index => rfl

theorem last_output (scalar : Nat) (bound : scalar<2^252) :
    (window scalar 125).output=model.coordinates (scalar • BalanceBlindingDomain670.represented) := by
  have final := FixedTraceAccess486.before_length (model.coordinates 0) (trace scalar) empty
  rw [trace_length] at final
  change (window scalar 125).output=GroupFixedWindows.fixedTraceOutput (model.coordinates 0) (trace scalar) at final
  exact final.trans (FixedTraceConstruction478.encoded_output (CapturedFirstSubgroup81.d:F) imaginary model
    (by rw [coefficient_eq];exact coefficient_no_unit_square) imaginary_square
    BalanceBlindingDomain670.represented 252 scalar bound)
end ShielddSecurity.BalanceBlindingLocal676

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingLocal676.trace_length
#print axioms ShielddSecurity.BalanceBlindingLocal676.trace_length

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingLocal676.window_equations
#print axioms ShielddSecurity.BalanceBlindingLocal676.window_equations

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingLocal676.add_equations
#print axioms ShielddSecurity.BalanceBlindingLocal676.add_equations

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingLocal676.bits
#print axioms ShielddSecurity.BalanceBlindingLocal676.bits

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingLocal676.before_positive
#print axioms ShielddSecurity.BalanceBlindingLocal676.before_positive

set_option pp.all true in
#check @ShielddSecurity.BalanceBlindingLocal676.last_output
#print axioms ShielddSecurity.BalanceBlindingLocal676.last_output
