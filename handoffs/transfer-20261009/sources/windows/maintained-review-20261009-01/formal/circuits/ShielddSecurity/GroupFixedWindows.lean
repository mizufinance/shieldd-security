import ShielddSecurity.TransferOwnership

set_option maxHeartbeats 300000

namespace ShielddSecurity.GroupFixedWindows

open Group

variable {F : Type} [Field F]

/-- Exact native `Point::add` formula used to build the fixed-base tables.
This is the shared-product inverse formula, before lifting its coordinates as
native circuit values. Its source/parameter identity remains a separate join. -/
def nativeAdd (d : F) (left right : Point F) : Point F :=
  let plus := 1 + delta d left right
  let minus := 1 - delta d left right
  let inverse := (plus * minus)⁻¹
  ⟨cross left right * minus * inverse,
   diagonal left right * plus * inverse⟩

/-- Complete-curve denominator facts discharge the inverse precondition in the
native table formula. No correctness of a witness-generation closure is assumed. -/
theorem native_add_affine (d imaginary : F) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (left right : Point F)
    (leftValid : OnCurve d left) (rightValid : OnCurve d right) :
    nativeAdd d left right = affineAdd d left right := by
  have denominators := denominators_nonzero d imaginary nonSquare imaginarySquare
    left right leftValid rightValid
  have inverseRow : ((1 + delta d left right) * (1 - delta d left right)) *
      ((1 + delta d left right) * (1 - delta d left right))⁻¹ = 1 :=
    mul_inv_cancel₀ (mul_ne_zero denominators.1 denominators.2)
  have rows := shared_inverse_rows d
    ((1 + delta d left right) * (1 - delta d left right))⁻¹
    left right (nativeAdd d left right) inverseRow rfl rfl
  exact affine_rows_sound d imaginary nonSquare imaginarySquare left right
    (nativeAdd d left right) leftValid rightValid rows.1 rows.2

theorem native_add_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (left right : J) :
    nativeAdd d (model.coordinates left) (model.coordinates right) =
      model.coordinates (left + right) := by
  calc
    _ = affineAdd d (model.coordinates left) (model.coordinates right) :=
      native_add_affine d imaginary nonSquare imaginarySquare _ _
        (model.onCurve left) (model.onCurve right)
    _ = model.coordinates (left + right) := (model.addition left right).symm

structure FixedWindowWitness (F : Type) where
  low : Bool
  high : Bool
  twice : Point F
  triple : Point F
  nextBase : Point F
  output : Point F

def fixedDigit (window : FixedWindowWitness F) : Nat :=
  window.low.toNat + 2 * window.high.toNat

/-- Three local native table computations; their scalar interpretation is a
conclusion of `fixed_table_coordinates`, not a hypothesis. -/
def FixedTableEquations (d : F) (base : Point F) (window : FixedWindowWitness F) : Prop :=
  window.twice = nativeAdd d base base ∧
  window.triple = nativeAdd d window.twice base ∧
  window.nextBase = nativeAdd d window.twice window.twice

def FixedWindowEquations (d : F) (input base : Point F)
    (window : FixedWindowWitness F) : Prop :=
  FixedTableEquations d base window ∧
  TransferOwnership.AddEquations d input
    (windowPoint (if window.low then 1 else 0) (if window.high then 1 else 0)
      base window.twice window.triple) window.output

/-- The native fixed table advances by four while the accumulator keeps its
current value. Both facts must survive a source/capture join for actual rows. -/
theorem fixed_table_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (base : J)
    (window : FixedWindowWitness F)
    (equations : FixedTableEquations d (model.coordinates base) window) :
    window.twice = model.coordinates (2 • base) ∧
    window.triple = model.coordinates (3 • base) ∧
    window.nextBase = model.coordinates (4 • base) := by
  have twiceEqual : window.twice = model.coordinates (2 • base) := by
    rw [two_nsmul]
    exact equations.1.trans
      (native_add_coordinates d imaginary model nonSquare imaginarySquare base base)
  have tripleEqual : window.triple = model.coordinates (3 • base) := by
    have tableStep := equations.2.1
    rw [twiceEqual, native_add_coordinates d imaginary model nonSquare imaginarySquare] at tableStep
    have count : 2 • base + base = (3 : Nat) • base := by
      simp only [show (3 : Nat) = 2 + 1 from rfl, add_nsmul, one_nsmul]
    exact tableStep.trans (congrArg model.coordinates count)
  have nextEqual : window.nextBase = model.coordinates (4 • base) := by
    have tableStep := equations.2.2
    rw [twiceEqual, native_add_coordinates d imaginary model nonSquare imaginarySquare] at tableStep
    have count : 2 • base + 2 • base = (4 : Nat) • base := by
      rw [← add_nsmul]
    exact tableStep.trans (congrArg model.coordinates count)
  exact ⟨twiceEqual, tripleEqual, nextEqual⟩

/-- Circuit addition quotient equations bind the selected native table entry
to the represented accumulator, with the table's new weighted base derived
from its local computations. Boolean selectors are explicit `Bool` inputs. -/
theorem fixed_window_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (acc base : J)
    (window : FixedWindowWitness F)
    (equations : FixedWindowEquations d (model.coordinates acc)
      (model.coordinates base) window) :
    window.output = model.coordinates (acc + fixedDigit window • base) ∧
    window.nextBase = model.coordinates (4 • base) := by
  obtain ⟨twiceEqual, tripleEqual, nextEqual⟩ := fixed_table_coordinates d imaginary
    model nonSquare imaginarySquare base window equations.1
  have rows := equations.2
  rw [twiceEqual, tripleEqual,
    TransferOwnership.selected_coordinates d model base window.low window.high] at rows
  exact ⟨TransferOwnership.add_coordinates d imaginary model nonSquare imaginarySquare
    acc (fixedDigit window • base) window.output rows.1 rows.2, nextEqual⟩

def FixedTraceEquations (d : F) : Point F → Point F → List (FixedWindowWitness F) → Prop
  | _, _, [] => True
  | input, base, window :: tail => FixedWindowEquations d input base window ∧
      FixedTraceEquations d window.output window.nextBase tail

def fixedTraceOutput : Point F → List (FixedWindowWitness F) → Point F
  | input, [] => input
  | _, window :: tail => fixedTraceOutput window.output tail

/-- Low-to-high symbolic induction derives the weighted-base invariant from
native table steps and circuit accumulator rows. It makes no assumption that
the output already equals a scalar multiplication. -/
theorem fixed_trace_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (windows : List (FixedWindowWitness F))
    (acc base : J)
    (equations : FixedTraceEquations d (model.coordinates acc) (model.coordinates base) windows) :
    fixedTraceOutput (model.coordinates acc) windows =
      model.coordinates (TransferWindows.fixedValue acc base (windows.map fixedDigit)) := by
  induction windows generalizing acc base with
  | nil => rfl
  | cons window tail ih =>
    obtain ⟨step, next⟩ := fixed_window_coordinates d imaginary model nonSquare
      imaginarySquare acc base window equations.1
    have remaining := equations.2
    rw [step, next] at remaining
    simpa only [fixedTraceOutput, List.map_cons, TransferWindows.fixedValue, step]
      using ih (acc + fixedDigit window • base) (4 • base) remaining

/-- The standard group's mathematical scalar follows from the already proved
generic recurrence, rather than an unrolled wide window constraint walk. -/
theorem fixed_trace_value_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (windows : List (FixedWindowWitness F))
    (acc base : J)
    (equations : FixedTraceEquations d (model.coordinates acc) (model.coordinates base) windows) :
    fixedTraceOutput (model.coordinates acc) windows =
      model.coordinates (acc + TransferWindows.digitsValue (windows.map fixedDigit) • base) := by
  rw [fixed_trace_coordinates d imaginary model nonSquare imaginarySquare windows acc base equations,
    TransferWindows.fixed_value]

/-- The explicit low-to-high iterator/bit-list correspondence includes the
runtime's false high bit for a final odd chunk. Actual bit rows, native lifting,
parameter identity and selected source roles remain separate obligations.
This theorem does not describe the separate native `Extended` multiplication. -/
theorem fixed_trace_scalar_coordinates {J : Type} [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (base : J)
    (windows : List (FixedWindowWitness F)) (bits : List Bool)
    (order : windows.map fixedDigit = TransferWindows.pairDigits bits)
    (equations : FixedTraceEquations d (model.coordinates 0) (model.coordinates base) windows) :
    fixedTraceOutput (model.coordinates 0) windows =
      model.coordinates (ShielddSecurity.binary bits • base) := by
  have trace := fixed_trace_value_coordinates d imaginary model nonSquare imaginarySquare
    windows 0 base equations
  rw [order, TransferWindows.pair_digits_value, zero_add] at trace
  exact trace

set_option pp.all true in
#check @native_add_affine
#print axioms native_add_affine
set_option pp.all true in
#check @native_add_coordinates
#print axioms native_add_coordinates
set_option pp.all true in
#check @fixed_table_coordinates
#print axioms fixed_table_coordinates
set_option pp.all true in
#check @fixed_window_coordinates
#print axioms fixed_window_coordinates
set_option pp.all true in
#check @fixed_trace_coordinates
#print axioms fixed_trace_coordinates
set_option pp.all true in
#check @fixed_trace_value_coordinates
#print axioms fixed_trace_value_coordinates
set_option pp.all true in
#check @fixed_trace_scalar_coordinates
#print axioms fixed_trace_scalar_coordinates

end ShielddSecurity.GroupFixedWindows
