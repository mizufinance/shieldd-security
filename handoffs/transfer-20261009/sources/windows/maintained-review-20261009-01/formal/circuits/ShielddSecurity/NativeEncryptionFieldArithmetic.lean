import ShielddSecurity.NativeEncryptionFixedArithmetic
import ShielddSecurity.TransferReduction

set_option maxHeartbeats 250000
set_option maxRecDepth 2048

namespace ShielddSecurity.NativeEncryptionFieldArithmetic

variable {F : Type} [Field F] [CharP F Scalar.modulus]

/-- One small modular squaring/multiplication certificate, with no large power. -/
theorem integer_step (before after : Int) (bit : Bool)
    (certificate : after % (Scalar.modulus : Int) =
      (before ^ 2 * (if bit then 5 else 1)) % (Scalar.modulus : Int)) :
    (after : F) = (before : F) ^ 2 * (if bit then (5 : F) else 1) := by
  have cast := congrArg (fun value : Int => (value : F)) certificate
  dsimp only at cast
  rw [Compiler.coefficient_mod (p := Scalar.modulus),
    Compiler.coefficient_mod (p := Scalar.modulus)] at cast
  cases bit <;> simpa only [Bool.false_eq_true, if_true, if_false, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat, Int.cast_one] using cast

/-- Symbolic composition of individually checked binary exponentiation steps. -/
theorem trace_value (limit : Nat) (bits : Nat → Bool)
    (exponents : Nat → Nat) (values : Nat → Int)
    (initialExponent : exponents 0 = 0) (initialValue : (values 0 : F) = 1)
    (exponentSteps : ∀ index, index < limit →
      exponents (index + 1) = exponents index * 2 + (if bits index then 1 else 0))
    (valueSteps : ∀ index, index < limit →
      (values (index + 1) : F) = (values index : F) ^ 2 * (if bits index then 5 else 1))
    (count : Nat) (bounded : count ≤ limit) :
    (values count : F) = (5 : F) ^ exponents count := by
  have all : ∀ count, count ≤ limit → (values count : F) = (5 : F) ^ exponents count := by
    intro count
    induction count with
    | zero =>
        intro small
        simpa only [initialExponent, pow_zero] using initialValue
    | succ index ih =>
        intro small
        have earlier : index < limit := by omega
        rw [valueSteps index earlier, ih (by omega), exponentSteps index earlier,
          pow_add, pow_mul]
        cases chosen : bits index <;> simp [chosen]
  exact all count bounded

/-- Characteristic is fixed by the canonical circuit field instance. -/
theorem odd_characteristic : ringChar F ≠ 2 := by
  rw [ringChar.eq F Scalar.modulus]
  decide

theorem five_nonzero : (5 : F) ≠ 0 :=
  NativeEncryptionFixedArithmetic.cast_nonzero 5 (by decide) (by decide)

/-- The endpoint premises are small integer certificates supplied by the
generated trace, not an assumed field Euler value. -/
theorem euler_from_trace [Fintype F] (codec : TransferReduction.CanonicalField F)
    (limit : Nat) (bits : Nat → Bool) (exponents : Nat → Nat) (values : Nat → Int)
    (initialExponent : exponents 0 = 0) (initialValue : (values 0 : F) = 1)
    (exponentSteps : ∀ index, index < limit →
      exponents (index + 1) = exponents index * 2 + (if bits index then 1 else 0))
    (valueSteps : ∀ index, index < limit →
      (values (index + 1) : F) = (values index : F) ^ 2 * (if bits index then 5 else 1))
    (lastExponent : exponents limit = Scalar.modulus / 2)
    (lastValue : values limit = (Scalar.modulus : Int) - 1) :
    (5 : F) ^ (Fintype.card F / 2) = -1 := by
  rw [TransferReduction.codec_cardinality codec]
  have result := trace_value limit bits exponents values initialExponent initialValue
    exponentSteps valueSteps limit (Nat.le_refl limit)
  rw [lastExponent, lastValue] at result
  have cast : (((Scalar.modulus : Int) - 1 : Int) : F) = -1 := by
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one,
      CharP.cast_eq_zero F Scalar.modulus, zero_sub]
  rw [cast] at result
  exact result.symm

set_option pp.all true in
#check @integer_step
#print axioms integer_step
set_option pp.all true in
#check @trace_value
#print axioms trace_value
set_option pp.all true in
#check @odd_characteristic
#print axioms odd_characteristic
set_option pp.all true in
#check @five_nonzero
#print axioms five_nonzero
set_option pp.all true in
#check @euler_from_trace
#print axioms euler_from_trace

end ShielddSecurity.NativeEncryptionFieldArithmetic
