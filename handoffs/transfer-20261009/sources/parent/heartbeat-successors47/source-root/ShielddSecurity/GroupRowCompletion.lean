-- GENERATED SOURCE-only by header_recipe47.py; all fresh audits UNRUN.
import ShielddSecurity.GroupExtended
import ShielddSecurity.ScalarCompletion

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupRowCompletion

variable {F : Type} [Field F]

/-- The general nonlinear Var::div lowering observed by
transfer_ownership.extract_rows: a fresh quotient witness, a materialized
quotient*denominator product, its difference-square auxiliary, and equality of
the product LC to the numerator. Constant-folded and square-specialized
lowerings require their own exact row transport and are not represented here.
The product LC may contain a fused remainder; its existing columns are kept. -/
def quotientRows (numerator denominator remainder : Linear)
    (quotient product auxiliary : Nat) : List Row :=
  ScalarCompletion.productRows [(quotient, 1)] denominator remainder product auxiliary ++
    [⟨Compiler.subtract ([(product, 1)] ++ remainder) numerator, []⟩]

def writes (quotient product auxiliary : Nat) : List Nat := [quotient, product, auxiliary]

def quotientValues (base : Nat → F) (numerator denominator remainder : Linear)
    (quotient product auxiliary column : Nat) : F :=
  if column = quotient then eval base numerator / eval base denominator
  else if column = product then eval base numerator - eval base remainder
  else if column = auxiliary then
    (eval base numerator / eval base denominator - eval base denominator) ^ 2
  else base column

def extendQuotient (base : Nat → F) (numerator denominator remainder : Linear)
    (quotient product auxiliary : Nat) : Nat → F :=
  patchAssignment base (quotientValues base numerator denominator remainder quotient product auxiliary)
    (writes quotient product auxiliary)

theorem extend_preserves (base : Nat → F) (numerator denominator remainder : Linear)
    (quotient product auxiliary column : Nat)
    (outside : column ∉ writes quotient product auxiliary) :
    extendQuotient base numerator denominator remainder quotient product auxiliary column =
      base column :=
  patchAssignment_preserves base _ _ column outside

theorem quotient_value (base : Nat → F) (numerator denominator remainder : Linear)
    (quotient product auxiliary : Nat) :
    extendQuotient base numerator denominator remainder quotient product auxiliary quotient =
      eval base numerator / eval base denominator := by
  simp [extendQuotient, patchAssignment, quotientValues, writes]

theorem eval_preserves (base : Nat → F) (numerator denominator remainder terms : Linear)
    (quotient product auxiliary : Nat)
    (outside : ∀ term ∈ terms, term.1 ∉ writes quotient product auxiliary) :
    eval (extendQuotient base numerator denominator remainder quotient product auxiliary) terms =
      eval base terms := by
  apply eval_agrees
  intro term member
  exact extend_preserves base numerator denominator remainder quotient product auxiliary term.1
    (outside term member)

/-- A legal denominator is the only semantic division precondition. Distinct
columns and input support freshness are ownership conditions, not assumptions
that an output quotient, product, or auxiliary already has its desired value. -/
theorem extend_complete (base : Nat → F) (numerator denominator remainder : Linear)
    (quotient product auxiliary : Nat)
    (quotientProduct : quotient ≠ product) (quotientAuxiliary : quotient ≠ auxiliary)
    (productAuxiliary : product ≠ auxiliary)
    (fresh : ∀ term ∈ numerator ++ denominator ++ remainder,
      term.1 ∉ writes quotient product auxiliary)
    (legal : eval base denominator ≠ 0) :
    Satisfies (extendQuotient base numerator denominator remainder quotient product auxiliary)
      (quotientRows numerator denominator remainder quotient product auxiliary) := by
  let rho := extendQuotient base numerator denominator remainder quotient product auxiliary
  have agrees (terms : Linear)
      (included : ∀ term ∈ terms, term ∈ numerator ++ denominator ++ remainder) :
      eval rho terms = eval base terms := by
    apply eval_preserves
    intro term member
    exact fresh term (included term member)
  have numeratorValue := agrees numerator (by intro term member; simp [member])
  have denominatorValue := agrees denominator (by intro term member; simp [member])
  have remainderValue := agrees remainder (by intro term member; simp [member])
  have quotientValue : rho quotient = eval base numerator / eval base denominator :=
    quotient_value base numerator denominator remainder quotient product auxiliary
  have productValue : rho product = eval base numerator - eval base remainder := by
    simp [rho, extendQuotient, patchAssignment, writes, quotientValues, Ne.symm quotientProduct]
  have auxiliaryValue : rho auxiliary =
      (eval base numerator / eval base denominator - eval base denominator) ^ 2 := by
    simp [rho, extendQuotient, patchAssignment, writes, quotientValues,
      Ne.symm quotientAuxiliary, Ne.symm productAuxiliary]
  have reciprocal : (eval base numerator / eval base denominator) * eval base denominator =
      eval base numerator := div_mul_cancel₀ _ legal
  simp only [rho] at numeratorValue denominatorValue remainderValue quotientValue productValue auxiliaryValue
  intro row present
  rcases List.mem_append.mp present with materialization | assertion
  · simp only [ScalarCompletion.productRows, List.mem_cons, List.not_mem_nil, or_false] at materialization
    rcases materialization with rfl | rfl
    · simp only [Square, Compiler.eval_subtract, eval, Int.cast_one, one_mul,
        add_zero, denominatorValue, quotientValue, auxiliaryValue]
      ring
    · simp only [Square, eval_append, eval_scale, eval, Int.cast_one, one_mul,
        add_zero, denominatorValue, remainderValue, quotientValue, productValue,
        auxiliaryValue, Int.cast_ofNat]
      calc
        _ = (eval base numerator / eval base denominator - eval base denominator) ^ 2 +
            4 * ((eval base numerator / eval base denominator) * eval base denominator) := by ring
        _ = _ := by rw [reciprocal]; ring
  · simp only [List.mem_singleton] at assertion
    subst row
    simp only [Square, Compiler.eval_subtract, eval_append, eval, Int.cast_one, one_mul,
      add_zero, numeratorValue, remainderValue, productValue]
    ring

/-- Other rows survive only when their actual supports exclude all three
writes. A surrounding-row satisfaction premise is used exclusively for this
preservation statement, not to manufacture the local quotient rows. -/
theorem preserves_rows (base : Nat → F) (numerator denominator remainder : Linear)
    (quotient product auxiliary : Nat) (prior : List Row)
    (satisfied : Satisfies base prior)
    (disjoint : ∀ row ∈ prior, ∀ term ∈ row.a ++ row.b,
      term.1 ∉ writes quotient product auxiliary) :
    Satisfies (extendQuotient base numerator denominator remainder quotient product auxiliary) prior :=
  patch_preserves_rows base _ _ prior satisfied disjoint

/-- Exact original-row transport requires complete finite coverage and a kept
constant-copy link. Hashes alone cannot discharge these algebraic conditions. -/
theorem original_rows_complete {p : Nat} [CharP F p]
    (base : Nat → F) (numerator denominator remainder : Linear)
    (quotient product auxiliary : Nat)
    (quotientProduct : quotient ≠ product) (quotientAuxiliary : quotient ≠ auxiliary)
    (productAuxiliary : product ≠ auxiliary)
    (fresh : ∀ term ∈ numerator ++ denominator ++ remainder,
      term.1 ∉ writes quotient product auxiliary)
    (legal : eval base denominator ≠ 0) (original : List Row) (copy : Nat)
    (zeroKept : 0 ∉ writes quotient product auxiliary)
    (copyKept : copy ∉ writes quotient product auxiliary) (linked : base copy = base 0)
    (coverage : ∀ actual ∈ original, ∃ expected ∈
      quotientRows numerator denominator remainder quotient product auxiliary,
      Compiler.canonical p (Compiler.unoutline copy actual.a) = Compiler.canonical p expected.a ∧
      Compiler.canonical p (Compiler.unoutline copy actual.b) = Compiler.canonical p expected.b) :
    Satisfies (extendQuotient base numerator denominator remainder quotient product auxiliary) original := by
  let rho := extendQuotient base numerator denominator remainder quotient product auxiliary
  have completed := extend_complete base numerator denominator remainder quotient product auxiliary
    quotientProduct quotientAuxiliary productAuxiliary fresh legal
  have copyLink : rho copy = rho 0 := by
    dsimp only [rho]
    rw [extend_preserves base numerator denominator remainder quotient product auxiliary copy copyKept,
      extend_preserves base numerator denominator remainder quotient product auxiliary 0 zeroKept, linked]
  intro actual member
  obtain ⟨expected, present, left, right⟩ := coverage actual member
  have result : Square (eval rho expected.a) (eval rho expected.b) := completed expected present
  rw [← Compiler.canonical_equal rho _ _ left, ← Compiler.canonical_equal rho _ _ right] at result
  simpa only [Compiler.eval_unoutline rho copy _ copyLink] using result

/-- The actual source numerator/denominator LC values are an explicit ingress
contract to be discharged by preceding source stages. The quotient coordinate
of the constructed assignment is derived here from complete-curve facts. -/
theorem complete_add_coordinate (d imaginary : F)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (left right : Group.Point F) (leftValid : Group.OnCurve d left)
    (rightValid : Group.OnCurve d right) (axisY : Bool)
    (base : Nat → F) (numerator denominator remainder : Linear)
    (quotient product auxiliary : Nat)
    (quotientProduct : quotient ≠ product) (quotientAuxiliary : quotient ≠ auxiliary)
    (productAuxiliary : product ≠ auxiliary)
    (fresh : ∀ term ∈ numerator ++ denominator ++ remainder,
      term.1 ∉ writes quotient product auxiliary)
    (numeratorValue : eval base numerator =
      if axisY then Group.diagonal left right else Group.cross left right)
    (denominatorValue : eval base denominator =
      if axisY then 1 - Group.delta d left right else 1 + Group.delta d left right) :
    Satisfies (extendQuotient base numerator denominator remainder quotient product auxiliary)
      (quotientRows numerator denominator remainder quotient product auxiliary) ∧
      extendQuotient base numerator denominator remainder quotient product auxiliary quotient =
        if axisY then (Group.affineAdd d left right).y else (Group.affineAdd d left right).x := by
  have denominators := Group.denominators_nonzero d imaginary nonSquare imaginarySquare
    left right leftValid rightValid
  have legal : eval base denominator ≠ 0 := by
    rw [denominatorValue]
    cases axisY
    · exact denominators.1
    · exact denominators.2
  refine ⟨extend_complete base numerator denominator remainder quotient product auxiliary
    quotientProduct quotientAuxiliary productAuxiliary fresh legal, ?_⟩
  rw [quotient_value, numeratorValue, denominatorValue]
  cases axisY <;> rfl

theorem complete_double_coordinate (d imaginary : F)
    (nonSquare : Group.NoUnitSquare d) (imaginarySquare : imaginary * imaginary = -1)
    (point : Group.Point F) (valid : Group.OnCurve d point) (axisY : Bool)
    (base : Nat → F) (numerator denominator remainder : Linear)
    (quotient product auxiliary : Nat)
    (quotientProduct : quotient ≠ product) (quotientAuxiliary : quotient ≠ auxiliary)
    (productAuxiliary : product ≠ auxiliary)
    (fresh : ∀ term ∈ numerator ++ denominator ++ remainder,
      term.1 ∉ writes quotient product auxiliary)
    (numeratorValue : eval base numerator =
      if axisY then Group.diagonal point point else GroupExtended.doubleNumerator point)
    (denominatorValue : eval base denominator =
      if axisY then GroupExtended.doubleYDenominator point else GroupExtended.doubleXDenominator point) :
    Satisfies (extendQuotient base numerator denominator remainder quotient product auxiliary)
      (quotientRows numerator denominator remainder quotient product auxiliary) ∧
      extendQuotient base numerator denominator remainder quotient product auxiliary quotient =
        if axisY then (Group.affineAdd d point point).y else (Group.affineAdd d point point).x := by
  have denominators := GroupExtended.optimized_denominators_nonzero d imaginary nonSquare
    imaginarySquare point valid
  have legal : eval base denominator ≠ 0 := by
    rw [denominatorValue]
    cases axisY
    · exact denominators.1
    · exact denominators.2
  have sound := GroupExtended.optimized_double_sound d imaginary nonSquare imaginarySquare point valid
  refine ⟨extend_complete base numerator denominator remainder quotient product auxiliary
    quotientProduct quotientAuxiliary productAuxiliary fresh legal, ?_⟩
  have coordinate : extendQuotient base numerator denominator remainder quotient product auxiliary quotient =
      if axisY then (GroupExtended.optimizedDouble point).y else (GroupExtended.optimizedDouble point).x := by
    rw [quotient_value, numeratorValue, denominatorValue]
    cases axisY <;> rfl
  rw [sound.1] at coordinate
  exact coordinate

set_option pp.all true in
#check @extend_preserves
#print axioms extend_preserves
set_option pp.all true in
#check @quotient_value
#print axioms quotient_value
set_option pp.all true in
#check @eval_preserves
#print axioms eval_preserves
set_option pp.all true in
#check @extend_complete
#print axioms extend_complete
set_option pp.all true in
#check @preserves_rows
#print axioms preserves_rows
set_option pp.all true in
#check @original_rows_complete
#print axioms original_rows_complete
set_option pp.all true in
#check @complete_add_coordinate
#print axioms complete_add_coordinate
set_option pp.all true in
#check @complete_double_coordinate
#print axioms complete_double_coordinate

end ShielddSecurity.GroupRowCompletion

set_option pp.all true in
#check @ShielddSecurity.GroupRowCompletion.quotientRows
#print axioms ShielddSecurity.GroupRowCompletion.quotientRows
set_option pp.all true in
#check @ShielddSecurity.GroupRowCompletion.writes
#print axioms ShielddSecurity.GroupRowCompletion.writes
set_option pp.all true in
#check @ShielddSecurity.GroupRowCompletion.quotientValues
#print axioms ShielddSecurity.GroupRowCompletion.quotientValues
set_option pp.all true in
#check @ShielddSecurity.GroupRowCompletion.extendQuotient
#print axioms ShielddSecurity.GroupRowCompletion.extendQuotient
