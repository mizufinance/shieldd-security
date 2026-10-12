import ShielddSecurity.Compiler
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedSeedShape265
abbrev Shape (column : Nat) : Prop := column=10 ∨ (49≤column ∧ column<134) ∨ 184≤column
end ShielddSecurity.SharedSeedShape265

set_option pp.all true in
#check @ShielddSecurity.SharedSeedShape265.Shape
#print axioms ShielddSecurity.SharedSeedShape265.Shape
