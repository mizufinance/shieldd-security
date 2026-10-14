import ShielddSecurity.SharedWordWitness221
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.RoutingParameterLayout863
def columns : List Nat := [19589,19590]
def flags : List Nat := []
def plain : List Nat := columns
def outside (column : Nat) : Bool := plain.all (fun target => decide (column≠target))
theorem alternatives (column : Nat) (member : column∈columns) : column=19589 ∨ column=19590 := by
  simpa only [columns,List.mem_cons,List.not_mem_nil,or_false] using member
theorem bounds (column : Nat) (member : column∈columns) : 19589≤column ∧ column<19591 := by
  have choices := alternatives column member
  omega
theorem plain_columns (column : Nat) (member : column∈plain) : column∈columns := member
end ShielddSecurity.RoutingParameterLayout863

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterLayout863.alternatives
#print axioms ShielddSecurity.RoutingParameterLayout863.alternatives

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterLayout863.bounds
#print axioms ShielddSecurity.RoutingParameterLayout863.bounds

set_option pp.all true in
#check @ShielddSecurity.RoutingParameterLayout863.plain_columns
#print axioms ShielddSecurity.RoutingParameterLayout863.plain_columns
