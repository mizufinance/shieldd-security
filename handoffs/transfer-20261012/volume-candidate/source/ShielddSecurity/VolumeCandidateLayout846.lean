import ShielddSecurity.SharedWordWitness221
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.VolumeCandidateLayout846
def columns : List Nat := List.range' 8127 128
def flags : List Nat := columns
def plain : List Nat := []
theorem bounds (column : Nat) (member : column∈columns) : 8127≤column ∧ column<8255 := by
  obtain ⟨offset,before,equal⟩ := List.mem_range'.mp member
  simp only [Nat.one_mul] at equal
  omega
theorem alternatives (column : Nat) (member : column∈columns) : 8127≤column ∧ column<8255 := bounds column member
theorem plain_columns (column : Nat) (member : column∈plain) : column∈columns := by
  simp only [plain,List.not_mem_nil] at member
end ShielddSecurity.VolumeCandidateLayout846

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateLayout846.bounds
#print axioms ShielddSecurity.VolumeCandidateLayout846.bounds

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateLayout846.alternatives
#print axioms ShielddSecurity.VolumeCandidateLayout846.alternatives

set_option pp.all true in
#check @ShielddSecurity.VolumeCandidateLayout846.plain_columns
#print axioms ShielddSecurity.VolumeCandidateLayout846.plain_columns
