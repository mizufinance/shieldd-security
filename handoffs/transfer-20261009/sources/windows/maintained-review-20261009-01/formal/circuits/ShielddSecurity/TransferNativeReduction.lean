import ShielddSecurity.Scalar

set_option maxHeartbeats 300000

namespace ShielddSecurity.TransferNativeReduction

def limbBase : Nat := 18446744073709551616

/-- Integer meaning of one u128 subtract-with-borrow step. Bounds ensure Rust's
wide computation neither underflows nor overflows; bit operations remain a
separate pinned machine-integer interpretation contract. -/
theorem limb_subtract (left right borrow : Nat)
    (leftBound : left < limbBase) (rightBound : right < limbBase)
    (borrowBound : borrow ≤ 1) :
    let wide := limbBase + left - right - borrow
    wide < 2 * limbBase ∧
      wide + right + borrow = limbBase + left ∧
      wide / limbBase ≤ 1 ∧
      (wide / limbBase = 0 ↔ left < right + borrow) ∧
      wide % limbBase < limbBase := by
  dsimp
  unfold limbBase at leftBound rightBound ⊢
  omega

theorem limb_borrow_equation (left right borrow : Nat)
    (leftBound : left < limbBase) (rightBound : right < limbBase)
    (borrowBound : borrow ≤ 1) :
    let wide := limbBase + left - right - borrow
    wide % limbBase + right + borrow =
      left + limbBase * (1 - wide / limbBase) := by
  have ⟨_, equation, quotientBound, _, _⟩ :=
    limb_subtract left right borrow leftBound rightBound borrowBound
  have split := Nat.mod_add_div (limbBase + left - right - borrow) limbBase
  dsimp at equation quotientBound ⊢
  unfold limbBase at equation quotientBound split ⊢
  omega

def limbs4 (a b c d : Nat) : Nat :=
  a + limbBase * b + limbBase ^ 2 * c + limbBase ^ 3 * d

/-- Four local borrow equations telescope without a whole-width constraint walk.
The first incoming borrow is zero, exactly as in scalar.rs. -/
theorem four_limb_borrow (a0 a1 a2 a3 o0 o1 o2 o3 d0 d1 d2 d3 b1 b2 b3 b4 : Nat)
    (step0 : d0 + o0 = a0 + limbBase * b1)
    (step1 : d1 + o1 + b1 = a1 + limbBase * b2)
    (step2 : d2 + o2 + b2 = a2 + limbBase * b3)
    (step3 : d3 + o3 + b3 = a3 + limbBase * b4) :
    limbs4 d0 d1 d2 d3 + limbs4 o0 o1 o2 o3 =
      limbs4 a0 a1 a2 a3 + limbBase ^ 4 * b4 := by
  simp only [limbs4, limbBase] at step0 step1 step2 step3 ⊢
  omega

theorem order_limbs :
    limbs4 15030498081868557495 11990869827041890434
      461402362329971456 1044189607433056169 = Scalar.order := by
  rfl

theorem final_borrow_select (value difference borrow : Nat)
    (valueBound : value < limbBase ^ 4) (differenceBound : difference < limbBase ^ 4)
    (borrowBound : borrow ≤ 1)
    (equation : difference + Scalar.order = value + limbBase ^ 4 * borrow) :
    (borrow = 0 ↔ Scalar.order ≤ value) ∧
      (if borrow = 0 then difference else value) =
        (if Scalar.order ≤ value then value - Scalar.order else value) ∧
      (1 - borrow = if Scalar.order ≤ value then 1 else 0) := by
  have zero : borrow = 0 ↔ Scalar.order ≤ value := by
    simp only [limbBase, Scalar.order] at valueBound differenceBound equation ⊢
    omega
  refine ⟨zero, ?_, ?_⟩
  · by_cases lower : Scalar.order ≤ value
    · have b := zero.mpr lower
      simp only [b, if_true, lower]
      simp only [b, Nat.mul_zero, Nat.add_zero] at equation
      omega
    · simp only [if_neg lower, if_neg (show borrow ≠ 0 from fun h => lower (zero.mp h))]
  · by_cases lower : Scalar.order ≤ value
    · simp [zero.mpr lower, lower]
    · have b : borrow = 1 := by have := zero.not.mpr lower; omega
      simp [b, lower]

/-- Numeric subtract-and-select recurrence. Agreement with the four-limb Rust
operation and the pinned canonical codec remains a separate source contract. -/
def rounds (order : Nat) : Nat → Nat → Nat × Nat
  | 0, value => (0, value)
  | fuel + 1, value =>
      if order ≤ value then
        let result := rounds order fuel (value - order)
        (result.1 + 1, result.2)
      else rounds order fuel value

/-- Rust updates its running quotient before the next round. -/
def roundsAccum (order : Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, quotient, value => (quotient, value)
  | fuel + 1, quotient, value =>
      if order ≤ value then roundsAccum order fuel (quotient + 1) (value - order)
      else roundsAccum order fuel quotient value

theorem accumulator_agreement (order fuel quotient value : Nat) :
    roundsAccum order fuel quotient value =
      (quotient + (rounds order fuel value).1, (rounds order fuel value).2) := by
  induction fuel generalizing quotient value with
  | zero => simp [roundsAccum, rounds]
  | succ fuel ih =>
      by_cases subtract : order ≤ value
      · simp only [roundsAccum, rounds, if_pos subtract]
        rw [ih]
        simp only [Nat.add_assoc, Nat.add_comm 1]
      · simp only [roundsAccum, rounds, if_neg subtract]
        exact ih quotient value

theorem rounds_complete (order fuel value : Nat) (positive : 0 < order)
    (bounded : value < (fuel + 1) * order) :
    value = (rounds order fuel value).1 * order + (rounds order fuel value).2 ∧
      (rounds order fuel value).1 ≤ fuel ∧
      (rounds order fuel value).2 < order := by
  induction fuel generalizing value with
  | zero => simp only [rounds, Nat.zero_mul, Nat.zero_add, Nat.zero_le]; simpa using bounded
  | succ fuel ih =>
      by_cases subtract : order ≤ value
      · have smaller : value - order < (fuel + 1) * order := by
          simp only [Nat.add_mul, Nat.one_mul] at bounded ⊢
          omega
        obtain ⟨equation, quotientBound, remainderBound⟩ := ih (value - order) smaller
        simp only [rounds, if_pos subtract, Nat.add_mul, Nat.one_mul]
        exact ⟨by omega, by omega, remainderBound⟩
      · have smaller : value < (fuel + 1) * order := by
          have factor : order ≤ (fuel + 1) * order := by
            simpa using Nat.mul_le_mul_right order (show 1 ≤ fuel + 1 by omega)
          omega
        obtain ⟨equation, quotientBound, remainderBound⟩ := ih value smaller
        simp only [rounds, if_neg subtract]
        exact ⟨equation, by omega, remainderBound⟩

theorem eight_rounds_complete (value : Nat) (canonical : value < Scalar.modulus) :
    Scalar.Reduction value (rounds Scalar.order 8 value).1
      (rounds Scalar.order 8 value).2 ∧ (rounds Scalar.order 8 value).1 ≤ 8 := by
  have positive : 0 < Scalar.order := by unfold Scalar.order; omega
  have bounded : value < (8 + 1) * Scalar.order := by
    simp only [Scalar.modulus, Scalar.order] at canonical ⊢
    omega
  obtain ⟨equation, quotientBound, remainderBound⟩ :=
    rounds_complete Scalar.order 8 value positive bounded
  exact ⟨⟨equation, remainderBound⟩, quotientBound⟩

/-- The native numeric recurrence and row-derived Euclidean pair agree whenever
they reduce the same canonical hash integer. No ownership/security conclusion. -/
theorem agrees_with_row_reduction (value quotient remainder : Nat)
    (canonical : value < Scalar.modulus)
    (rowReduction : Scalar.Reduction value quotient remainder) :
    (rounds Scalar.order 8 value).1 = quotient ∧
      (rounds Scalar.order 8 value).2 = remainder := by
  exact Scalar.reduction_unique (eight_rounds_complete value canonical).1 rowReduction

set_option pp.all true in
#check @limb_subtract
#print axioms limb_subtract
set_option pp.all true in
#check @limb_borrow_equation
#print axioms limb_borrow_equation
set_option pp.all true in
#check @four_limb_borrow
#print axioms four_limb_borrow
set_option pp.all true in
#check @order_limbs
#print axioms order_limbs
set_option pp.all true in
#check @final_borrow_select
#print axioms final_borrow_select
set_option pp.all true in
#check @agrees_with_row_reduction
#print axioms agrees_with_row_reduction
set_option pp.all true in
#check @accumulator_agreement
#print axioms accumulator_agreement
set_option pp.all true in
#check @rounds_complete
#print axioms rounds_complete
set_option pp.all true in
#check @eight_rounds_complete
#print axioms eight_rounds_complete

end ShielddSecurity.TransferNativeReduction
