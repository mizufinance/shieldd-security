import ShielddSecurity.ScalarBits

set_option maxHeartbeats 100000

namespace ShielddSecurity.ScalarBitFieldSemantics

variable {F : Type} [Field F]

/-- An owned field assignment of a Boolean constructs its original Boolean
row; the Boolean row is not an input to the constructor. -/
theorem field_square (rho : Nat → F) (terms : Linear) (bit : Bool)
    (value : eval rho terms = if bit then (1 : F) else 0) :
    Square (eval rho terms) (eval rho terms) := by
  rw [value]
  cases bit <;> simp [Square]

/-- The decoder used by the existing actual arithmetic trace recovers the
independently written source bit, including false. -/
theorem field_decoded (rho : Nat → F) (terms : Linear) (bit : Bool)
    (value : eval rho terms = if bit then (1 : F) else 0) :
    ScalarBits.decodeBit rho terms = bit := by
  classical
  unfold ScalarBits.decodeBit
  rw [value]
  cases bit <;> simp

set_option pp.all true in
#check @field_square
#print axioms field_square
set_option pp.all true in
#check @field_decoded
#print axioms field_decoded

end ShielddSecurity.ScalarBitFieldSemantics
