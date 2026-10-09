import ShielddSecurity.NativeEncryptionInitializationComplete

set_option maxHeartbeats 200000

namespace ShielddSecurity.NativeEncryptionInitializationLiteral

variable {F : Type} [Field F]

/-- A finite scaled-square certificate transfers an independently proved
nonsquare coefficient. No long exponent walk or chosen native sqrt is needed. -/
theorem scaled_nonsquare (coefficient value factor : F)
    (nonSquare : Group.NoUnitSquare coefficient) (nonzero : value ≠ 0)
    (certificate : coefficient * factor * factor = value) : ¬ IsSquare value := by
  rintro ⟨root, rootSquare⟩
  have rootNonzero : root ≠ 0 := by
    intro zero
    apply nonzero
    simpa only [zero, zero_mul] using rootSquare
  apply nonSquare (factor * root⁻¹)
  calc
    coefficient * (factor * root⁻¹) * (factor * root⁻¹) =
        (coefficient * factor * factor) * (root⁻¹ * root⁻¹) := by ring
    _ = value * (root⁻¹ * root⁻¹) := by rw [certificate]
    _ = (root * root) * (root⁻¹ * root⁻¹) := by rw [rootSquare]
    _ = 1 := by field_simp [rootNonzero] <;> ring

theorem choice_false (api : ElligatorNativeRoots.SqrtAPI F) (value : F)
    (notSquare : ¬ IsSquare value) : ElligatorNativeRoots.choice api value = false := by
  have absent : ElligatorNativeRoots.choice api value ≠ true := by
    intro present
    exact notSquare ((api.complete value).mp present)
  cases observed : ElligatorNativeRoots.choice api value
  · rfl
  · exact False.elim (absent observed)

theorem choice_true (api : ElligatorNativeRoots.SqrtAPI F) (value root : F)
    (certificate : root * root = value) : ElligatorNativeRoots.choice api value = true :=
  (api.complete value).mpr ⟨root, certificate.symm⟩

/-- The owned sign rule identifies a finite literal from its independently
checked square and canonical parity. The API's raw root is never requested. -/
theorem normalized_literal [CharP F Scalar.modulus] [Fintype F]
    (codec : TransferReduction.CanonicalField F) (api : ElligatorNativeRoots.SqrtAPI F)
    (odd : ringChar F ≠ 2) (fiveNonzero : (5 : F) ≠ 0)
    (fiveEuler : (5 : F) ^ (Fintype.card F / 2) = -1)
    (u first candidate : F) (branch : Bool) (firstNonzero : first ≠ 0)
    (choiceValue : ElligatorNativeRoots.choice api first = branch)
    (square : candidate * candidate = if branch then first else 5 * u * u * first)
    (parity : codec.decode candidate % 2 = if branch then 1 else 0) :
    ElligatorNativeParity.normalizeRoot codec (ElligatorNativeRoots.choice api first)
      (ElligatorNativeRoots.rootValue api (ElligatorNativeRoots.selectedValue api 5 u first)) = candidate := by
  have computed := (ElligatorNativeRoots.computed_roots api odd 5 u first fiveNonzero fiveEuler).2
  have normalized := ElligatorNativeParity.selected_normalization codec
    (ElligatorNativeRoots.choice api first) first (5 * u * u * first)
    (ElligatorNativeRoots.rootValue api (ElligatorNativeRoots.selectedValue api 5 u first))
    firstNonzero computed
  apply ElligatorNative.codec_root_unique codec
  · calc
      _ = (if ElligatorNativeRoots.choice api first then first else 5 * u * u * first) := normalized.1
      _ = (if branch then first else 5 * u * u * first) := by rw [choiceValue]
      _ = candidate * candidate := square.symm
  · rw [normalized.2, choiceValue]
    exact parity.symm

theorem rational_literal [DecidableEq F] (s t inverse x y : F)
    (unit : ((s + 1) * t) * inverse = 1)
    (xValue : inverse * (s + 1) * s = x)
    (yValue : inverse * t * (s - 1) = y) :
    Elligator.rationalPoint s t = ⟨x,y⟩ := by
  have nonzero : (s + 1) * t ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at unit
    exact zero_ne_one unit
  have inverseValue : ((s + 1) * t)⁻¹ = inverse := inv_eq_of_mul_eq_one_right unit
  simp only [Elligator.rationalPoint, if_neg nonzero, inverseValue, xValue, yValue]

theorem double_literal (d : F) (point : Group.Point F) (inverse x y : F)
    (unit : ((1 + Group.delta d point point) * (1 - Group.delta d point point)) * inverse = 1)
    (xValue : Group.cross point point * (1 - Group.delta d point point) * inverse = x)
    (yValue : Group.diagonal point point * (1 + Group.delta d point point) * inverse = y) :
    GroupFixedWindows.nativeAdd d point point = ⟨x,y⟩ := by
  have inverseValue : ((1 + Group.delta d point point) * (1 - Group.delta d point point))⁻¹ = inverse :=
    inv_eq_of_mul_eq_one_right unit
  simp only [GroupFixedWindows.nativeAdd, inverseValue, xValue, yValue]

set_option pp.all true in
#check @scaled_nonsquare
#print axioms scaled_nonsquare
set_option pp.all true in
#check @choice_false
#print axioms choice_false
set_option pp.all true in
#check @choice_true
#print axioms choice_true
set_option pp.all true in
#check @normalized_literal
#print axioms normalized_literal
set_option pp.all true in
#check @rational_literal
#print axioms rational_literal
set_option pp.all true in
#check @double_literal
#print axioms double_literal

end ShielddSecurity.NativeEncryptionInitializationLiteral
