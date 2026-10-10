import ShielddSecurity.Arithmetic

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace ShielddSecurity.Scalar

/-- Circuit field and Jubjub subgroup order are different primes. These are
the concrete integers used by scalar.rs; their source/row binding is separate. -/
def modulus : Nat := 52435875175126190479447740508185965837690552500527637822603658699938581184513
def order : Nat := 6554484396890773809930967563523245729705921265872317281365359162392183254199
def lastRemainder : Nat := modulus - 1 - 8 * order

/-- Independent Euclidean reduction contract. The quotient-eight guard is
essential: q≤8 and r<order alone still allow wrapping the circuit field. -/
def Reduction (value quotient remainder : Nat) : Prop :=
  value = quotient * order + remainder ∧ remainder < order

theorem reduction_sum_bound {quotient remainder : Nat}
    (quotientBound : quotient ≤ 8) (remainderBound : remainder < order)
    (lastBound : quotient = 8 → remainder ≤ lastRemainder) :
    quotient * order + remainder < modulus := by
  by_cases last : quotient = 8
  · have edge := lastBound last
    subst quotient
    simp only [lastRemainder, modulus, order] at edge ⊢
    omega
  · have small : quotient ≤ 7 := by omega
    have productBound := Nat.mul_le_mul_right order small
    simp only [modulus, order] at remainderBound productBound ⊢
    omega

/-- All assignments satisfying the exact arithmetic premises have integer
Euclidean meaning. The bit/comparator rows must establish the bounds; an honest
Rust quotient/remainder constructor is not a premise of this theorem. -/
theorem reduction_sound {F : Type} [Field F] [CharP F modulus]
    (value quotient remainder : Nat) (valueBound : value < modulus)
    (quotientBound : quotient ≤ 8) (remainderBound : remainder < order)
    (lastBound : quotient = 8 → remainder ≤ lastRemainder)
    (equation : (quotient : F) * (order : F) + (remainder : F) = (value : F)) :
    Reduction value quotient remainder := by
  have lifted := bounded_cast_injective (F := F) (p := modulus)
    (reduction_sum_bound quotientBound remainderBound lastBound) valueBound
    (by simpa using equation)
  exact ⟨lifted.symm, remainderBound⟩

/-- Every canonical circuit-field integer admits legal reduction operands,
including the final short quotient-eight interval. No hash inverse is assumed. -/
theorem reduction_complete {F : Type} [Field F] (value : Nat)
    (valueBound : value < modulus) :
    ∃ quotient remainder : Nat,
      quotient ≤ 8 ∧ remainder < order ∧
      (quotient = 8 → remainder ≤ lastRemainder) ∧
      Reduction value quotient remainder ∧
      (quotient : F) * (order : F) + (remainder : F) = (value : F) := by
  have remainderBound := Nat.mod_lt value (by decide : 0 < order)
  have division := Nat.mod_add_div value order
  have quotientBound : value / order ≤ 8 := by
    simp only [modulus, order] at valueBound remainderBound division ⊢
    omega
  have lastBound : value / order = 8 → value % order ≤ lastRemainder := by
    intro last
    rw [last] at division
    simp only [lastRemainder, modulus, order] at valueBound division ⊢
    omega
  have meaning : value = (value / order) * order + value % order := by
    simpa [Nat.mul_comm, Nat.add_comm] using division.symm
  refine ⟨value / order, value % order, quotientBound, remainderBound, lastBound,
    ⟨meaning, remainderBound⟩, ?_⟩
  simpa using congrArg (fun n : Nat => (n : F)) meaning.symm

theorem reduction_unique {value q1 q2 r1 r2 : Nat}
    (first : Reduction value q1 r1) (second : Reduction value q2 r2) :
    q1 = q2 ∧ r1 = r2 := by
  rcases first with ⟨eq1, bound1⟩
  rcases second with ⟨eq2, bound2⟩
  simp only [order] at eq1 eq2 bound1 bound2
  omega

/-- Explicit underconstraint witness: without the quotient-eight upper edge,
the modular equation admits value zero with a nonzero remainder. -/
theorem omitted_last_bound_wraps {F : Type} [Field F] [CharP F modulus] :
    0 < modulus - 8 * order ∧ modulus - 8 * order < order ∧
    ¬ modulus - 8 * order ≤ lastRemainder ∧
    (8 : F) * (order : F) + ((modulus - 8 * order : Nat) : F) = 0 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  have integer : 8 * order + (modulus - 8 * order) = modulus := by decide
  have casted := congrArg (fun n : Nat => (n : F)) integer
  change ((8 * order + (modulus - 8 * order) : Nat) : F) = (modulus : F) at casted
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, CharP.cast_eq_zero F modulus] at casted
  exact casted

/-- Independent ordered-prefix comparison. A new most-significant bit decides
the order if unequal, otherwise the prior lower-prefix comparison is retained. -/
def comparisonStep (lower left right : Bool) : Bool :=
  if left == right then lower else right

def comparisonPolynomial {F : Type} [Field F] (lower left right : F) : F :=
  let both := (1 - left) * right
  both + lower * ((1 - left) + right - (both + both))

theorem comparison_polynomial_correct {F : Type} [Field F] (lower left right : Bool) :
    comparisonPolynomial (if lower then (1 : F) else 0)
      (if left then 1 else 0) (if right then 1 else 0) =
      (if comparisonStep lower left right then 1 else 0) := by
  cases lower <;> cases left <;> cases right <;>
    simp [comparisonPolynomial, comparisonStep]

/-- This is the integer invariant of the actual little-endian comparator loop.
The bound is on each lower prefix, not an assumption of the desired comparison.
Actual source/row certificates must supply the bit and prefix reconstruction. -/
theorem comparison_step_order (weight a b : Nat) (aBound : a < weight) (bBound : b < weight)
    (lower left right : Bool) (previous : lower = true ↔ a ≤ b) :
    comparisonStep lower left right = true ↔
      a + (if left then weight else 0) ≤ b + (if right then weight else 0) := by
  cases left <;> cases right
  · simpa [comparisonStep] using previous
  · simp [comparisonStep]; omega
  · simp [comparisonStep]; omega
  · simpa [comparisonStep] using previous

/-- Little-endian prefix value. This is a recurrence over actual Boolean bits;
the comparator theorem does not take an assumed integer bound as its result. -/
def prefixValue (bits : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => prefixValue bits n + (if bits n then 2 ^ n else 0)

def prefixComparison (left right : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => comparisonStep (prefixComparison left right n) (left n) (right n)

theorem prefix_value_bound (bits : Nat → Bool) (n : Nat) :
    prefixValue bits n < 2 ^ n := by
  induction n with
  | zero => simp [prefixValue]
  | succ n ih =>
      cases bit : bits n <;> simp only [prefixValue, bit, Bool.false_eq_true,
        ↓reduceIte, Nat.pow_succ] <;> omega

theorem prefix_comparison_order (left right : Nat → Bool) (n : Nat) :
    prefixComparison left right n = true ↔ prefixValue left n ≤ prefixValue right n := by
  induction n with
  | zero => simp [prefixComparison, prefixValue]
  | succ n ih =>
      exact comparison_step_order (2 ^ n) (prefixValue left n) (prefixValue right n)
        (prefix_value_bound left n) (prefix_value_bound right n)
        (prefixComparison left right n) (left n) (right n) ih

/-- Local row certificates supply these polynomial equations. Induction then
determines every prefix, including its Booleanity, for arbitrary assignments.
There is no honest execution or desired comparator result premise. -/
theorem comparison_chain_sound {F : Type} [Field F]
    (left right : Nat → Bool) (state : Nat → F) (n : Nat)
    (initial : state 0 = 1)
    (steps : ∀ i < n, state (i + 1) = comparisonPolynomial (state i)
      (if left i then 1 else 0) (if right i then 1 else 0)) :
    state n = (if prefixComparison left right n then 1 else 0) ∧
      (state n = 1 ↔ prefixValue left n ≤ prefixValue right n) := by
  have values : ∀ m, m ≤ n → state m = (if prefixComparison left right m then 1 else 0) := by
    intro m
    induction m with
    | zero => intro _; simpa [prefixComparison] using initial
    | succ m ih =>
        intro bound
        rw [steps m (by omega), ih (by omega), comparison_polynomial_correct]
        rfl
  have value := values n (Nat.le_refl n)
  refine ⟨value, ?_⟩
  rw [value]
  have decode : (if prefixComparison left right n then (1 : F) else 0) = 1 ↔
      prefixComparison left right n = true := by
    cases prefixComparison left right n <;> simp
  exact decode.trans (prefix_comparison_order left right n)

/-- The row-derived quotient and remainder construct a canonical integer for
an arbitrary hash-output field wire. No canonical representation or honest
native reduction is assumed. The actual inverse constraint separately rules
out a zero reduced scalar. The generator must derive every bound and equality
below from its exact range/comparison/reconstruction rows. -/
theorem reduction_representation {F : Type} [Field F]
    (hash inverse : F) (quotient remainder : Nat)
    (quotientBound : quotient ≤ 8) (remainderBound : remainder < order)
    (lastBound : quotient = 8 → remainder ≤ lastRemainder)
    (equation : (quotient : F) * (order : F) + (remainder : F) = hash)
    (nonzeroRow : (remainder : F) * inverse = 1) :
    ∃ value : Nat, value < modulus ∧ (value : F) = hash ∧
      Reduction value quotient remainder ∧ remainder ≠ 0 := by
  refine ⟨quotient * order + remainder,
    reduction_sum_bound quotientBound remainderBound lastBound, ?_,
    ⟨rfl, remainderBound⟩, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_mul] using equation
  · intro zero
    subst remainder
    simp at nonzeroRow

/-- Once actual rows construct the canonical representative, its uniqueness
uses the circuit characteristic and bound; a field wire cannot be assigned
two different canonical integers by different reduction witnesses. -/
theorem canonical_representative_unique {F : Type} [Field F] [CharP F modulus]
    (hash : F) (first second : Nat)
    (firstBound : first < modulus) (secondBound : second < modulus)
    (firstValue : (first : F) = hash) (secondValue : (second : F) = hash) :
    first = second :=
  bounded_cast_injective (F := F) (p := modulus) firstBound secondBound
    (firstValue.trans secondValue.symm)


end ShielddSecurity.Scalar

set_option pp.all true in
#check @ShielddSecurity.Scalar.modulus
#print axioms ShielddSecurity.Scalar.modulus
set_option pp.all true in
#check @ShielddSecurity.Scalar.order
#print axioms ShielddSecurity.Scalar.order
set_option pp.all true in
#check @ShielddSecurity.Scalar.lastRemainder
#print axioms ShielddSecurity.Scalar.lastRemainder
set_option pp.all true in
#check @ShielddSecurity.Scalar.Reduction
#print axioms ShielddSecurity.Scalar.Reduction
set_option pp.all true in
#check @ShielddSecurity.Scalar.reduction_sum_bound
#print axioms ShielddSecurity.Scalar.reduction_sum_bound
set_option pp.all true in
#check @ShielddSecurity.Scalar.reduction_sound
#print axioms ShielddSecurity.Scalar.reduction_sound
set_option pp.all true in
#check @ShielddSecurity.Scalar.reduction_complete
#print axioms ShielddSecurity.Scalar.reduction_complete
set_option pp.all true in
#check @ShielddSecurity.Scalar.reduction_unique
#print axioms ShielddSecurity.Scalar.reduction_unique
set_option pp.all true in
#check @ShielddSecurity.Scalar.omitted_last_bound_wraps
#print axioms ShielddSecurity.Scalar.omitted_last_bound_wraps
set_option pp.all true in
#check @ShielddSecurity.Scalar.comparisonStep
#print axioms ShielddSecurity.Scalar.comparisonStep
set_option pp.all true in
#check @ShielddSecurity.Scalar.comparisonPolynomial
#print axioms ShielddSecurity.Scalar.comparisonPolynomial
set_option pp.all true in
#check @ShielddSecurity.Scalar.comparison_polynomial_correct
#print axioms ShielddSecurity.Scalar.comparison_polynomial_correct
set_option pp.all true in
#check @ShielddSecurity.Scalar.comparison_step_order
#print axioms ShielddSecurity.Scalar.comparison_step_order
set_option pp.all true in
#check @ShielddSecurity.Scalar.prefixValue
#print axioms ShielddSecurity.Scalar.prefixValue
set_option pp.all true in
#check @ShielddSecurity.Scalar.prefixComparison
#print axioms ShielddSecurity.Scalar.prefixComparison
set_option pp.all true in
#check @ShielddSecurity.Scalar.prefix_value_bound
#print axioms ShielddSecurity.Scalar.prefix_value_bound
set_option pp.all true in
#check @ShielddSecurity.Scalar.prefix_comparison_order
#print axioms ShielddSecurity.Scalar.prefix_comparison_order
set_option pp.all true in
#check @ShielddSecurity.Scalar.comparison_chain_sound
#print axioms ShielddSecurity.Scalar.comparison_chain_sound
set_option pp.all true in
#check @ShielddSecurity.Scalar.reduction_representation
#print axioms ShielddSecurity.Scalar.reduction_representation
set_option pp.all true in
#check @ShielddSecurity.Scalar.canonical_representative_unique
#print axioms ShielddSecurity.Scalar.canonical_representative_unique
