import ShielddSecurity.SharedWordWitness221
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.VolumeBoundaryLayout833
def columns : List Nat := [7739,8255]
def flags : List Nat := [8255]
def plain : List Nat := [7739]
def outside (column : Nat) : Bool := plain.all (fun target => decide (column≠target))
theorem alternatives (column : Nat) (member : column∈columns) : column=7739 ∨ column=8255 := by
  simpa only [columns,List.mem_cons,List.not_mem_nil,or_false] using member
theorem bounds (column : Nat) (member : column∈columns) : 7739≤column ∧ column<8256 := by
  have choices := alternatives column member
  omega
theorem plain_columns (column : Nat) (member : column∈plain) : column∈columns := by
  have checked : plain.all (fun col => decide (col∈columns))=true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp checked column member)
end ShielddSecurity.VolumeBoundaryLayout833

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryLayout833.alternatives
#print axioms ShielddSecurity.VolumeBoundaryLayout833.alternatives

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryLayout833.bounds
#print axioms ShielddSecurity.VolumeBoundaryLayout833.bounds

set_option pp.all true in
#check @ShielddSecurity.VolumeBoundaryLayout833.plain_columns
#print axioms ShielddSecurity.VolumeBoundaryLayout833.plain_columns
