import ShielddSecurity.SharedWordWitness221
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.VolumePathLayout933
def columns : List Nat := List.range' 8388 72
def flags : List Nat := []
def plain : List Nat := columns
def outside (column : Nat) : Bool := plain.all (fun target => decide (column≠target))
theorem bounds (column : Nat) (member : column∈columns) : 8388≤column ∧ column<8460 := by
  obtain ⟨i,inside,equal⟩ := List.mem_range'.mp member
  simp only [Nat.one_mul] at equal
  omega
theorem alternatives (column : Nat) (member : column∈columns) : 8388≤column ∧ column<8460 := bounds column member
theorem plain_columns (column : Nat) (member : column∈plain) : column∈columns := member
end ShielddSecurity.VolumePathLayout933

set_option pp.all true in
#check @ShielddSecurity.VolumePathLayout933.alternatives
#print axioms ShielddSecurity.VolumePathLayout933.alternatives

set_option pp.all true in
#check @ShielddSecurity.VolumePathLayout933.bounds
#print axioms ShielddSecurity.VolumePathLayout933.bounds

set_option pp.all true in
#check @ShielddSecurity.VolumePathLayout933.plain_columns
#print axioms ShielddSecurity.VolumePathLayout933.plain_columns
