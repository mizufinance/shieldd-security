import ShielddSecurity.SharedWordWitness221
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.VolumeHashLayout883
def columns : List Nat := [7740, 8385, 8386, 8508, 8509, 8510]
def flags : List Nat := []
def plain : List Nat := columns
def outside (column : Nat) : Bool := plain.all (fun target => decide (column≠target))
theorem alternatives (column : Nat) (member : column∈columns) : column=7740 ∨ column=8385 ∨ column=8386 ∨ column=8508 ∨ column=8509 ∨ column=8510 := by
  simpa only [columns,List.mem_cons,List.not_mem_nil,or_false] using member
theorem bounds (column : Nat) (member : column∈columns) : 7740≤column ∧ column<8511 := by
  have choices := alternatives column member
  omega
theorem plain_columns (column : Nat) (member : column∈plain) : column∈columns := member
end ShielddSecurity.VolumeHashLayout883

set_option pp.all true in
#check @ShielddSecurity.VolumeHashLayout883.alternatives
#print axioms ShielddSecurity.VolumeHashLayout883.alternatives

set_option pp.all true in
#check @ShielddSecurity.VolumeHashLayout883.bounds
#print axioms ShielddSecurity.VolumeHashLayout883.bounds

set_option pp.all true in
#check @ShielddSecurity.VolumeHashLayout883.plain_columns
#print axioms ShielddSecurity.VolumeHashLayout883.plain_columns
