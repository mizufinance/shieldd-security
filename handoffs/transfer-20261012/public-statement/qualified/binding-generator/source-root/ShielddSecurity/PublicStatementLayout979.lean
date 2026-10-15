/- GENERATED from the maintained public-statement binding generator. Edit the generator, then regenerate. -/
import ShielddSecurity.RegistryNaturalSeed298
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.PublicStatementLayout979
def columns : List Nat := [4272,4273,3,4920,4921,6324,6325,19848,19849,19589,8509,8510,7739,7607,4532,4785,4,5,8511,8512,8513,8514,8515,8516,8517,8519,8520,8521,8522,8523,8524,8525,8526,8527,8528,8530,8531,8532,8533,8534,8535,8536,7,8518,8529,8537,8538,8539,8540,8543,8544,8545,8546,8542,8547,8548,8549,8550,10079,10080,10081,10082]
def inputColumns : List Nat := [4272,4273,3,4920,4921,6324,6325,195230,195234,19848,19849,19589,8509,8510,7739,7607,4532,4785,4,5,8511,8512,8513,8514,8515,8516,8517,8519,8520,8521,8522,8523,8524,8525,8526,8527,8528,8530,8531,8532,8533,8534,8535,8536,7,8518,8529,8537,8538,8539,8540,8543,8544,8545,8546,8542,8547,8548,8549,8550,10079,10080,10081,10082]
theorem input_count : inputColumns.length=64 := rfl
theorem stored_count : columns.length=62 := rfl
theorem zero_outside : 0∉columns := by decide +kernel
theorem net_x_outside : 195230∉columns := by decide +kernel
theorem net_y_outside : 195234∉columns := by decide +kernel
theorem claimed_outside : 22737∉columns := by decide +kernel
theorem bounds (column : Nat) (member : column∈columns) : 3≤column ∧ column≤19849 := by
  simp only [columns,List.mem_cons,List.not_mem_nil,or_false] at member
  omega
end ShielddSecurity.PublicStatementLayout979


set_option pp.all true in
#check @ShielddSecurity.PublicStatementLayout979.input_count
#print axioms ShielddSecurity.PublicStatementLayout979.input_count

set_option pp.all true in
#check @ShielddSecurity.PublicStatementLayout979.stored_count
#print axioms ShielddSecurity.PublicStatementLayout979.stored_count

set_option pp.all true in
#check @ShielddSecurity.PublicStatementLayout979.zero_outside
#print axioms ShielddSecurity.PublicStatementLayout979.zero_outside

set_option pp.all true in
#check @ShielddSecurity.PublicStatementLayout979.net_x_outside
#print axioms ShielddSecurity.PublicStatementLayout979.net_x_outside

set_option pp.all true in
#check @ShielddSecurity.PublicStatementLayout979.net_y_outside
#print axioms ShielddSecurity.PublicStatementLayout979.net_y_outside

set_option pp.all true in
#check @ShielddSecurity.PublicStatementLayout979.claimed_outside
#print axioms ShielddSecurity.PublicStatementLayout979.claimed_outside

set_option pp.all true in
#check @ShielddSecurity.PublicStatementLayout979.bounds
#print axioms ShielddSecurity.PublicStatementLayout979.bounds
