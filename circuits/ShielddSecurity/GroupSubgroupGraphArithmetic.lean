import ShielddSecurity.GroupNativeSubgroupWitness

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.GroupSubgroupGraphArithmetic
variable {F : Type} [Field F]

/-! Arithmetic meaning of the exact seven-node curve block and seventeen-node
shared-inverse doubling block. The three doublings compose by a symbolic
recurrence. A separate typed source-graph matcher must transport the actual
node equations/assertions into this interface; this file supplies no row or
graph identity claim and assumes no desired curve/eightfold conclusion. -/

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
    hint = GroupNativeSubgroupWitness.sharedInverse d point := by
  have nonzero : inverseProduct d point ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at equation
    exact zero_ne_one equation
  have divided : hint = 1 / inverseProduct d point :=
    (eq_div_iff nonzero).mpr (by simpa only [mul_comm] using equation)
  simpa only [one_div, inverseProduct, GroupNativeSubgroupWitness.sharedInverse] using divided

theorem hint_step_sound (d : F) (point : Group.Point F) (hint : F)
    (equation : inverseProduct d point * hint = 1) :
    hintStep d point hint = GroupFixedWindows.nativeAdd d point point := by
  rw [inverse_hint_unique d point hint equation]
  rfl

theorem double_assertion_sound (d negative : F) (point : Group.Point F) (hint : F)
    (negativeOne : negative = -1) (asserted : doubleValues d negative point hint 8 = 1) :
    doubleOutput d negative point hint = GroupFixedWindows.nativeAdd d point point := by
  rw [negativeOne, double_inverse_value] at asserted
  rw [negativeOne, double_output_value]
  exact hint_step_sound d point hint asserted

theorem double_assertion_complete (d negative : F) (point : Group.Point F)
    (negativeOne : negative = -1) (nonzero : inverseProduct d point ≠ 0) :
    doubleValues d negative point (GroupNativeSubgroupWitness.sharedInverse d point) 8 = 1 := by
  rw [negativeOne, double_inverse_value]
  exact mul_inv_cancel₀ nonzero

theorem native_double_assertion (d imaginary negative : F) (point : Group.Point F)
    (negativeOne : negative = -1) (nonSquare : Group.NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (valid : Group.OnCurve d point) :
    doubleValues d negative point (GroupNativeSubgroupWitness.sharedInverse d point) 8 = 1 := by
  rw [negativeOne, double_inverse_value]
  exact (GroupNativeSubgroupWitness.native_double_constraints d imaginary nonSquare imaginarySquare point valid).1

def hintTrace (d : F) (initial : Group.Point F) (hints : Nat → F) : Nat → Group.Point F
  | 0 => initial
  | count + 1 => hintStep d (hintTrace d initial hints count) (hints count)

def nativeTrace (d : F) (initial : Group.Point F) : Nat → Group.Point F
  | 0 => initial
  | count + 1 =>
      let previous := nativeTrace d initial count
      GroupFixedWindows.nativeAdd d previous previous

def nativeHints (d : F) (initial : Group.Point F) (count : Nat) : F :=
  GroupNativeSubgroupWitness.sharedInverse d (nativeTrace d initial count)

theorem constructed_trace_native (d : F) (initial : Group.Point F) (count : Nat) :
    hintTrace d initial (nativeHints d initial) count = nativeTrace d initial count := by
  induction count with
  | zero => rfl
  | succ count previous =>
      simp only [hintTrace, nativeTrace, previous, nativeHints]
      rfl

theorem asserted_trace_native (d negative : F) (initial : Group.Point F) (hints : Nat → F)
    (count : Nat) (negativeOne : negative = -1)
    (asserted : ∀ index < count,
      doubleValues d negative (hintTrace d initial hints index) (hints index) 8 = 1) :
    hintTrace d initial hints count = nativeTrace d initial count := by
  induction count with
  | zero => rfl
  | succ count previous =>
      have earlier := previous (by intro index before; exact asserted index (by omega))
      have inverseEq := asserted count (by omega)
      rw [negativeOne, double_inverse_value] at inverseEq
      rw [hintTrace, nativeTrace, hint_step_sound d _ _ inverseEq, earlier]

theorem native_trace_three (d : F) (initial : Group.Point F) :
    nativeTrace d initial 3 = GroupNativeCofactor.nativeEight d initial := rfl

def SourceAssertions (d negative : F) (point preimage : Group.Point F) (hints : Nat → F) : Prop :=
  curveValues d negative preimage 3 = curveValues d negative preimage 6 ∧
    (∀ index < 3, doubleValues d negative (hintTrace d preimage hints index) (hints index) 8 = 1) ∧
    point.x = (hintTrace d preimage hints 3).x ∧
    point.y = (hintTrace d preimage hints 3).y

theorem source_assertions_sound (d negative : F) (point preimage : Group.Point F)
    (hints : Nat → F) (negativeOne : negative = -1)
    (asserted : SourceAssertions d negative point preimage hints) :
    Group.OnCurve d preimage ∧ GroupNativeCofactor.nativeEight d preimage = point := by
  have computed := asserted_trace_native d negative preimage hints 3 negativeOne asserted.2.1
  refine ⟨(curve_assertion_iff d negative preimage negativeOne).mp asserted.1, ?_⟩
  rw [← native_trace_three, ← computed]
  exact congrArg₂ Group.Point.mk asserted.2.2.1.symm asserted.2.2.2.symm

theorem source_assertions_complete (d negative : F) (preimage : Group.Point F)
    (negativeOne : negative = -1) (valid : Group.OnCurve d preimage)
    (denominators : ∀ index < 3, inverseProduct d (nativeTrace d preimage index) ≠ 0) :
    SourceAssertions d negative (GroupNativeCofactor.nativeEight d preimage) preimage
      (nativeHints d preimage) := by
  refine ⟨(curve_assertion_iff d negative preimage negativeOne).mpr valid, ?_, ?_, ?_⟩
  · intro index before
    rw [constructed_trace_native]
    exact double_assertion_complete d negative _ negativeOne (denominators index before)
  · rw [constructed_trace_native, native_trace_three]
  · rw [constructed_trace_native, native_trace_three]

set_option pp.all true in
#check @curve_assertion_iff
#print axioms curve_assertion_iff
set_option pp.all true in
#check @double_inverse_value
#print axioms double_inverse_value
set_option pp.all true in
#check @double_output_value
#print axioms double_output_value
set_option pp.all true in
#check @inverse_hint_unique
#print axioms inverse_hint_unique
set_option pp.all true in
#check @hint_step_sound
#print axioms hint_step_sound
set_option pp.all true in
#check @double_assertion_sound
#print axioms double_assertion_sound
set_option pp.all true in
#check @double_assertion_complete
#print axioms double_assertion_complete
set_option pp.all true in
#check @native_double_assertion
#print axioms native_double_assertion
set_option pp.all true in
#check @constructed_trace_native
#print axioms constructed_trace_native
set_option pp.all true in
#check @asserted_trace_native
#print axioms asserted_trace_native
set_option pp.all true in
#check @native_trace_three
#print axioms native_trace_three
set_option pp.all true in
#check @source_assertions_sound
#print axioms source_assertions_sound
set_option pp.all true in
#check @source_assertions_complete
#print axioms source_assertions_complete

end ShielddSecurity.GroupSubgroupGraphArithmetic
