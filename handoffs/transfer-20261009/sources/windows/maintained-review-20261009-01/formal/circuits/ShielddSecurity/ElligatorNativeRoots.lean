import ShielddSecurity.ElligatorNativeParity
import Mathlib.FieldTheory.Finite.Basic

set_option maxHeartbeats 180000

namespace ShielddSecurity.ElligatorNativeRoots

/-- Functional contract of the pinned native square-root operation. This is an
explicit imported interface, not an assertion that a particular circuit root
or output is correct. Its native implementation join is separate. -/
structure SqrtAPI (F : Type) [Field F] where
  sqrt : F → Option F
  sound : ∀ value root, sqrt value = some root → root * root = value
  complete : ∀ value, (sqrt value).isSome = true ↔ IsSquare value

variable {F : Type} [Field F]

def choice (api : SqrtAPI F) (first : F) : Bool := (api.sqrt first).isSome

def qrValue (api : SqrtAPI F) (z first : F) : F :=
  if choice api first then first else z * first

def selectedValue (api : SqrtAPI F) (z u first : F) : F :=
  if choice api first then first else z * u * u * first

def rootValue (api : SqrtAPI F) (value : F) : F := (api.sqrt value).getD 0

/-- The nonsquare branch has a square fallback over the exact finite field.
The Euler equation and characteristic restriction are global parameter facts. -/
theorem alternative_square [Fintype F] (odd : ringChar F ≠ 2)
    (z first : F) (zNonzero : z ≠ 0)
    (euler : z ^ (Fintype.card F / 2) = -1) (notSquare : ¬ IsSquare first) :
    IsSquare (z * first) := by
  have firstNonzero : first ≠ 0 := by
    intro zero
    apply notSquare
    exact ⟨0,by simp only [zero,mul_zero]⟩
  have negative : first ^ (Fintype.card F / 2) = -1 := by
    rcases FiniteField.pow_dichotomy odd firstNonzero with positive | negative
    · exact False.elim (notSquare ((FiniteField.isSquare_iff odd firstNonzero).mpr positive))
    · exact negative
  apply (FiniteField.isSquare_iff odd (mul_ne_zero zNonzero firstNonzero)).mpr
  rw [mul_pow,euler,negative]
  ring

theorem qr_square [Fintype F] (api : SqrtAPI F) (odd : ringChar F ≠ 2)
    (z first : F) (zNonzero : z ≠ 0) (euler : z ^ (Fintype.card F / 2) = -1) :
    IsSquare (qrValue api z first) := by
  by_cases chosen : choice api first = true
  · simpa only [qrValue,chosen,if_true] using (api.complete first).mp chosen
  · have absent : ¬ IsSquare first := by
      intro square
      exact chosen ((api.complete first).mpr square)
    simpa only [qrValue,if_neg chosen] using alternative_square odd z first zNonzero euler absent

theorem selected_square [Fintype F] (api : SqrtAPI F) (odd : ringChar F ≠ 2)
    (z u first : F) (zNonzero : z ≠ 0) (euler : z ^ (Fintype.card F / 2) = -1) :
    IsSquare (selectedValue api z u first) := by
  by_cases chosen : choice api first = true
  · simpa only [selectedValue,chosen,if_true] using (api.complete first).mp chosen
  · have absent : ¬ IsSquare first := by
      intro square
      exact chosen ((api.complete first).mpr square)
    obtain ⟨root,square⟩ := alternative_square odd z first zNonzero euler absent
    refine ⟨u * root,?_⟩
    simp only [selectedValue,if_neg chosen]
    calc
      z * u * u * first = u * u * (z * first) := by ring
      _ = (u * root) * (u * root) := by rw [square]; ring

theorem root_value_square (api : SqrtAPI F) (value : F) (square : IsSquare value) :
    rootValue api value * rootValue api value = value := by
  have sqrtPresent := (api.complete value).mpr square
  cases observed : api.sqrt value with
  | none =>
      have impossible : (none : Option F).isSome = true := by
        simpa only [observed] using sqrtPresent
      cases impossible
  | some root =>
      have sound := api.sound value root observed
      simpa only [rootValue,observed,Option.getD_some] using sound

/-- Both roots are computed by the native operation. No chosen root equation
is supplied for a particular map input, including u=0 in the false branch. -/
theorem computed_roots [Fintype F] (api : SqrtAPI F) (odd : ringChar F ≠ 2)
    (z u first : F) (zNonzero : z ≠ 0) (euler : z ^ (Fintype.card F / 2) = -1) :
    rootValue api (qrValue api z first) * rootValue api (qrValue api z first) =
        (if choice api first then first else z * first) ∧
      rootValue api (selectedValue api z u first) * rootValue api (selectedValue api z u first) =
        (if choice api first then first else z * u * u * first) :=
  ⟨root_value_square api _ (qr_square api odd z first zNonzero euler),
   root_value_square api _ (selected_square api odd z u first zNonzero euler)⟩

set_option pp.all true in
#check @alternative_square
#print axioms alternative_square
set_option pp.all true in
#check @qr_square
#print axioms qr_square
set_option pp.all true in
#check @selected_square
#print axioms selected_square
set_option pp.all true in
#check @root_value_square
#print axioms root_value_square
set_option pp.all true in
#check @computed_roots
#print axioms computed_roots

end ShielddSecurity.ElligatorNativeRoots
