import ShielddSecurity.Group
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CompilerSubgroupArithmetic79
variable {F : Type} [Field F]
def curveValues (d negative : F) (point : Group.Point F) : Nat → F
  | 0 => point.x * point.x
  | 1 => point.y * point.y
  | 2 => negative * (point.x * point.x)
  | 3 => point.y * point.y + negative * (point.x * point.x)
  | 4 => d * (point.x * point.x)
  | 5 => (d * (point.x * point.x)) * (point.y * point.y)
  | 6 => 1 + (d * (point.x * point.x)) * (point.y * point.y)
  | _ => 0

def doubleValues (d negative : F) (point : Group.Point F) (hint : F) : Nat → F :=
  let xx := point.x * point.x
  let yy := point.y * point.y
  let delta := xx * yy * d
  let plus := 1 + delta
  let minus := 1 + negative * delta
  fun index => match index with
    | 0 => xx
    | 1 => yy
    | 2 => xx * yy
    | 3 => delta
    | 4 => plus
    | 5 => negative * delta
    | 6 => minus
    | 7 => plus * minus
    | 8 => plus * minus * hint
    | 9 => point.x * point.y
    | 10 => point.y * point.x
    | 11 => point.x * point.y + point.y * point.x
    | 12 => (point.x * point.y + point.y * point.x) * minus
    | 13 => (point.x * point.y + point.y * point.x) * minus * hint
    | 14 => yy + xx
    | 15 => (yy + xx) * plus
    | 16 => (yy + xx) * plus * hint
    | _ => 0

def inverseProduct (d : F) (point : Group.Point F) : F :=
  (1 + Group.delta d point point) * (1 - Group.delta d point point)

def hintStep (d : F) (point : Group.Point F) (hint : F) : Group.Point F :=
  ⟨Group.cross point point * (1 - Group.delta d point point) * hint,
    Group.diagonal point point * (1 + Group.delta d point point) * hint⟩

def doubleOutput (d negative : F) (point : Group.Point F) (hint : F) : Group.Point F :=
  ⟨doubleValues d negative point hint 13, doubleValues d negative point hint 16⟩

theorem curve_assertion_iff (d negative : F) (point : Group.Point F)
    (negativeOne : negative = -1) :
    curveValues d negative point 3 = curveValues d negative point 6 ↔
      Group.OnCurve d point := by
  rw [negativeOne]
  simp only [curveValues, Group.OnCurve, neg_one_mul, ← sub_eq_add_neg]
  congr 1 <;> ring

theorem double_inverse_value (d : F) (point : Group.Point F) (hint : F) :
    doubleValues d (-1) point hint 8 = inverseProduct d point * hint := by
  simp only [doubleValues, inverseProduct, Group.delta]
  ring

theorem double_output_value (d : F) (point : Group.Point F) (hint : F) :
    doubleOutput d (-1) point hint = hintStep d point hint := by
  apply congrArg₂ Group.Point.mk <;>
    simp only [doubleOutput, doubleValues, hintStep, Group.cross, Group.diagonal, Group.delta] <;> ring

theorem inverse_hint_unique (d : F) (point : Group.Point F) (hint : F)
    (equation : inverseProduct d point * hint = 1) :
    hint = (inverseProduct d point)⁻¹ := by
  have nonzero : inverseProduct d point ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at equation
    exact zero_ne_one equation
  have divided : hint = 1 / inverseProduct d point :=
    (eq_div_iff nonzero).mpr (by simpa only [mul_comm] using equation)
  simpa only [one_div] using divided

def double (d : F) (point : Group.Point F) : Group.Point F :=
  hintStep d point (inverseProduct d point)⁻¹

theorem hint_step_sound (d : F) (point : Group.Point F) (hint : F)
    (equation : inverseProduct d point * hint = 1) :
    hintStep d point hint = double d point := by
  rw [inverse_hint_unique d point hint equation]
  rfl

theorem double_assertion_sound (d negative : F) (point : Group.Point F) (hint : F)
    (negativeOne : negative = -1) (asserted : doubleValues d negative point hint 8 = 1) :
    doubleOutput d negative point hint = double d point := by
  rw [negativeOne, double_inverse_value] at asserted
  rw [negativeOne, double_output_value]
  exact hint_step_sound d point hint asserted

theorem double_assertion_complete (d negative : F) (point : Group.Point F)
    (negativeOne : negative = -1) (nonzero : inverseProduct d point ≠ 0) :
    doubleValues d negative point ((inverseProduct d point)⁻¹) 8 = 1 := by
  rw [negativeOne, double_inverse_value]
  exact mul_inv_cancel₀ nonzero

theorem curve_double_assertion (d imaginary negative : F) (point : Group.Point F)
    (negativeOne : negative = -1) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (valid : Group.OnCurve d point) :
    doubleValues d negative point ((inverseProduct d point)⁻¹) 8 = 1 := by
  rw [negativeOne, double_inverse_value]
  have denoms := Group.denominators_nonzero d imaginary nonSquare imaginarySquare point point valid valid
  exact double_assertion_complete d negative point negativeOne (mul_ne_zero denoms.1 denoms.2)

def hintTrace (d : F) (initial : Group.Point F) (hints : Nat → F) : Nat → Group.Point F
  | 0 => initial
  | count + 1 => hintStep d (hintTrace d initial hints count) (hints count)

def trace (d : F) (initial : Group.Point F) : Nat → Group.Point F
  | 0 => initial
  | count + 1 =>
      let previous := trace d initial count
      double d previous

def hints (d : F) (initial : Group.Point F) (count : Nat) : F :=
  (inverseProduct d (trace d initial count))⁻¹

theorem constructed_trace (d : F) (initial : Group.Point F) (count : Nat) :
    hintTrace d initial (hints d initial) count = trace d initial count := by
  induction count with
  | zero => rfl
  | succ count previous =>
      simp only [hintTrace, trace, previous, hints]
      rfl

theorem asserted_trace (d negative : F) (initial : Group.Point F) (hints : Nat → F)
    (count : Nat) (negativeOne : negative = -1)
    (asserted : ∀ index < count,
      doubleValues d negative (hintTrace d initial hints index) (hints index) 8 = 1) :
    hintTrace d initial hints count = trace d initial count := by
  induction count with
  | zero => rfl
  | succ count previous =>
      have earlier := previous (by intro index before; exact asserted index (by omega))
      have inverseEq := asserted count (by omega)
      rw [negativeOne, double_inverse_value] at inverseEq
      rw [hintTrace, trace, hint_step_sound d _ _ inverseEq, earlier]

def eight (d : F) (initial : Group.Point F) : Group.Point F := trace d initial 3

theorem trace_three (d : F) (initial : Group.Point F) :
    trace d initial 3 = eight d initial := rfl

def SourceAssertions (d negative : F) (point preimage : Group.Point F) (hints : Nat → F) : Prop :=
  curveValues d negative preimage 3 = curveValues d negative preimage 6 ∧
    (∀ index < 3, doubleValues d negative (hintTrace d preimage hints index) (hints index) 8 = 1) ∧
    point.x = (hintTrace d preimage hints 3).x ∧
    point.y = (hintTrace d preimage hints 3).y

theorem source_assertions_sound (d negative : F) (point preimage : Group.Point F)
    (hints : Nat → F) (negativeOne : negative = -1)
    (asserted : SourceAssertions d negative point preimage hints) :
    Group.OnCurve d preimage ∧ eight d preimage = point := by
  have computed := asserted_trace d negative preimage hints 3 negativeOne asserted.2.1
  refine ⟨(curve_assertion_iff d negative preimage negativeOne).mp asserted.1, ?_⟩
  rw [← trace_three, ← computed]
  exact congrArg₂ Group.Point.mk asserted.2.2.1.symm asserted.2.2.2.symm

theorem source_assertions_complete (d negative : F) (preimage : Group.Point F)
    (negativeOne : negative = -1) (valid : Group.OnCurve d preimage)
    (denominators : ∀ index < 3, inverseProduct d (trace d preimage index) ≠ 0) :
    SourceAssertions d negative (eight d preimage) preimage
      (hints d preimage) := by
  refine ⟨(curve_assertion_iff d negative preimage negativeOne).mpr valid, ?_, ?_, ?_⟩
  · intro index before
    rw [constructed_trace]
    exact double_assertion_complete d negative _ negativeOne (denominators index before)
  · rw [constructed_trace, trace_three]
  · rw [constructed_trace, trace_three]

theorem double_affine (d : F) (point : Group.Point F)
    (nonzero : inverseProduct d point≠0) : double d point=Group.affineAdd d point point := by
  have denoms := mul_ne_zero_iff.mp nonzero
  have inv : inverseProduct d point*(inverseProduct d point)⁻¹=1 := mul_inv_cancel₀ nonzero
  apply congrArg₂ Group.Point.mk
  · apply Group.quotient_sound _ _ _ denoms.1
    change (Group.cross point point*(1-Group.delta d point point)*(inverseProduct d point)⁻¹)*
      (1+Group.delta d point point)=Group.cross point point
    calc
      _ = Group.cross point point*(inverseProduct d point*(inverseProduct d point)⁻¹) := by unfold inverseProduct; ring
      _ = _ := by rw [inv,mul_one]
  · apply Group.quotient_sound _ _ _ denoms.2
    change (Group.diagonal point point*(1+Group.delta d point point)*(inverseProduct d point)⁻¹)*
      (1-Group.delta d point point)=Group.diagonal point point
    calc
      _ = Group.diagonal point point*(inverseProduct d point*(inverseProduct d point)⁻¹) := by unfold inverseProduct; ring
      _ = _ := by rw [inv,mul_one]
end ShielddSecurity.CompilerSubgroupArithmetic79
