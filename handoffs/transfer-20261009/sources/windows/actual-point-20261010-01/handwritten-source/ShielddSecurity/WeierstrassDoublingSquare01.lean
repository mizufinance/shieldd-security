import ShielddSecurity.Range

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.WeierstrassDoublingSquare01

variable {F : Type} [Field F]

/-- The polynomial identity underlying the tangent formula for
y² = x³ + a x² + b x. No division or concrete point representation is used. -/
theorem tangent_doubling_identity (a b x y slope : F)
    (equation : y * y = x * x * x + a * x * x + b * x)
    (tangent : 2 * y * slope = 3 * x * x + 2 * a * x + b) :
    (slope * slope - a - 2 * x) * ((2 * y) * (2 * y)) =
      (x * x - b) * (x * x - b) := by
  calc
    _ = (2 * y * slope) * (2 * y * slope) -
        4 * (a + 2 * x) * (y * y) := by ring
    _ = (3 * x * x + 2 * a * x + b) * (3 * x * x + 2 * a * x + b) -
        4 * (a + 2 * x) * (x * x * x + a * x * x + b * x) := by rw [tangent, equation]
    _ = _ := by ring

/-- A regular tangent double has square X coordinate. The concrete addition
law must separately establish the equation, tangent row, nonzero denominator
and identification of this expression with its output coordinate. -/
theorem tangent_output_square (a b x y slope : F) (two : (2 : F) ≠ 0)
    (nonzeroY : y ≠ 0)
    (equation : y * y = x * x * x + a * x * x + b * x)
    (tangent : 2 * y * slope = 3 * x * x + 2 * a * x + b) :
    ∃ root : F, root * root = slope * slope - a - 2 * x := by
  have denominator : 2 * y ≠ 0 := mul_ne_zero two nonzeroY
  refine ⟨(x * x - b) / (2 * y), ?_⟩
  apply mul_right_cancel₀ (mul_ne_zero denominator denominator)
  calc
    _ = (((x * x - b) / (2 * y)) * (2 * y)) *
        (((x * x - b) / (2 * y)) * (2 * y)) := by ring
    _ = (x * x - b) * (x * x - b) := by rw [div_mul_cancel₀ _ denominator]
    _ = _ := (tangent_doubling_identity a b x y slope equation tangent).symm

end ShielddSecurity.WeierstrassDoublingSquare01

set_option pp.all true in
#check @ShielddSecurity.WeierstrassDoublingSquare01.tangent_doubling_identity
#print axioms ShielddSecurity.WeierstrassDoublingSquare01.tangent_doubling_identity
set_option pp.all true in
#check @ShielddSecurity.WeierstrassDoublingSquare01.tangent_output_square
#print axioms ShielddSecurity.WeierstrassDoublingSquare01.tangent_output_square
