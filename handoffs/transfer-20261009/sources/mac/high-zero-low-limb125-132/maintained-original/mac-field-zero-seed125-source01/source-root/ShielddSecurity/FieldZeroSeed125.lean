import ShielddSecurity.Range
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FieldZeroSeed125
variable {F : Type} [Field F]
noncomputable def flag (delta : F) : F := by
  classical
  exact if delta=0 then 1 else 0
noncomputable def seeded (base : Nat → F) (start : Nat) (delta : F) (column : Nat) : F :=
  if column=start then flag delta else if column=start+1 then delta⁻¹ else base column
theorem outside (base : Nat → F) (start : Nat) (delta : F) (column : Nat)
    (bound : column<start ∨ start+2≤column) : seeded base start delta column=base column := by
  have h : column≠start := by omega
  have k : column≠start+1 := by omega
  simp only [seeded,if_neg h,if_neg k]
theorem flag_value (base : Nat → F) (start : Nat) (delta : F) :
    seeded base start delta start=flag delta := by simp only [seeded,if_true]
theorem inverse_value (base : Nat → F) (start : Nat) (delta : F) :
    seeded base start delta (start+1)=delta⁻¹ := by
  simp only [seeded,show ¬start+1=start by omega,if_false,if_true]
theorem boolean (delta : F) : Square (flag delta) (flag delta) := by
  classical
  by_cases h : delta=0 <;> simp [flag,h,Square]
theorem inverse (delta : F) : delta*delta⁻¹=1-flag delta := by
  classical
  by_cases h : delta=0
  · simp [flag,h]
  · simp [flag,h,mul_inv_cancel₀ h]
theorem annihilated (delta : F) : delta*flag delta=0 := by
  classical
  by_cases h : delta=0 <;> simp [flag,h]
end ShielddSecurity.FieldZeroSeed125

set_option pp.all true in
#check @ShielddSecurity.FieldZeroSeed125.flag
#print axioms ShielddSecurity.FieldZeroSeed125.flag
set_option pp.all true in
#check @ShielddSecurity.FieldZeroSeed125.seeded
#print axioms ShielddSecurity.FieldZeroSeed125.seeded
set_option pp.all true in
#check @ShielddSecurity.FieldZeroSeed125.outside
#print axioms ShielddSecurity.FieldZeroSeed125.outside
set_option pp.all true in
#check @ShielddSecurity.FieldZeroSeed125.flag_value
#print axioms ShielddSecurity.FieldZeroSeed125.flag_value
set_option pp.all true in
#check @ShielddSecurity.FieldZeroSeed125.inverse_value
#print axioms ShielddSecurity.FieldZeroSeed125.inverse_value
set_option pp.all true in
#check @ShielddSecurity.FieldZeroSeed125.boolean
#print axioms ShielddSecurity.FieldZeroSeed125.boolean
set_option pp.all true in
#check @ShielddSecurity.FieldZeroSeed125.inverse
#print axioms ShielddSecurity.FieldZeroSeed125.inverse
set_option pp.all true in
#check @ShielddSecurity.FieldZeroSeed125.annihilated
#print axioms ShielddSecurity.FieldZeroSeed125.annihilated
