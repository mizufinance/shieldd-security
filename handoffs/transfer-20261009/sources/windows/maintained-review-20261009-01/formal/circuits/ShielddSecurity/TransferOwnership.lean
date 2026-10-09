import ShielddSecurity.GroupWindows
import ShielddSecurity.TransferWindows

set_option maxHeartbeats 300000

namespace ShielddSecurity.TransferOwnership
open Group

/-- The actual optimized doubling quotient equations determine the represented
point. Curve validity is carried by the standard model; division rows alone
would allow arbitrary 0/0. Runtime parameter and source/row joins are separate. -/
theorem double_coordinates {F J : Type} [Field F] [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (point : J) (output : Point F)
    (xRow : output.x * ((model.coordinates point).y * (model.coordinates point).y -
        (model.coordinates point).x * (model.coordinates point).x) =
      ((model.coordinates point).x + (model.coordinates point).y) *
        ((model.coordinates point).x + (model.coordinates point).y) -
        (model.coordinates point).x * (model.coordinates point).x -
        (model.coordinates point).y * (model.coordinates point).y)
    (yRow : output.y * (2 - ((model.coordinates point).y * (model.coordinates point).y -
        (model.coordinates point).x * (model.coordinates point).x)) =
      (model.coordinates point).y * (model.coordinates point).y +
        (model.coordinates point).x * (model.coordinates point).x) :
    output = model.coordinates (2 • point) := by
  have sound := double_rows_sound d imaginary nonSquare imaginarySquare
    (model.coordinates point) output (model.onCurve point) xRow yRow
  rw [two_nsmul, model.addition]
  exact sound.1

/-- The variable-base runtime addition uses independent quotient witnesses,
not the shared-inverse cofactor addition used by the AK constructor. -/
theorem add_coordinates {F J : Type} [Field F] [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (left right : J) (output : Point F)
    (xRow : output.x * (1 + delta d (model.coordinates left) (model.coordinates right)) =
      ((model.coordinates left).x + (model.coordinates left).y) *
        ((model.coordinates right).x + (model.coordinates right).y) -
        (model.coordinates left).x * (model.coordinates right).x -
        (model.coordinates left).y * (model.coordinates right).y)
    (yRow : output.y * (1 - delta d (model.coordinates left) (model.coordinates right)) =
      (model.coordinates left).y * (model.coordinates right).y +
        (model.coordinates left).x * (model.coordinates right).x) :
    output = model.coordinates (left + right) := by
  have crossRow : output.x * (1 + delta d (model.coordinates left) (model.coordinates right)) =
      cross (model.coordinates left) (model.coordinates right) := by
    rw [xRow]
    unfold cross
    ring
  have sound := affine_rows_sound d imaginary nonSquare imaginarySquare
    (model.coordinates left) (model.coordinates right) output
    (model.onCurve left) (model.onCurve right) crossRow yRow
  rw [model.addition]
  exact sound

theorem selected_coordinates {F J : Type} [Field F] [AddCommGroup J]
    (d : F) (model : StandardCurveModel J d) (base : J) (low high : Bool) :
    windowPoint (if low then 1 else 0) (if high then 1 else 0)
      (model.coordinates base) (model.coordinates (2 • base)) (model.coordinates (3 • base)) =
      model.coordinates ((low.toNat + 2 * high.toNat) • base) := by
  rw [window_correct]
  cases low <;> cases high <;>
    simp [windowCase, model.identity, one_nsmul]

def DoubleEquations {F : Type} [Field F] (input output : Point F) : Prop :=
  output.x * (input.y * input.y - input.x * input.x) =
    (input.x + input.y) * (input.x + input.y) - input.x * input.x - input.y * input.y ∧
  output.y * (2 - (input.y * input.y - input.x * input.x)) =
    input.y * input.y + input.x * input.x

def AddEquations {F : Type} [Field F] (d : F) (left right output : Point F) : Prop :=
  output.x * (1 + delta d left right) =
    (left.x + left.y) * (right.x + right.y) - left.x * right.x - left.y * right.y ∧
  output.y * (1 - delta d left right) = left.y * right.y + left.x * right.x

/-- One window composes both optimized doubles and its addition, preserving the
represented accumulator. Actual row extraction and selector-formula equality
must establish these arithmetic equations before this lemma is applicable. -/
theorem window_coordinates {F J : Type} [Field F] [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (acc base : J) (low high : Bool)
    (first second output : Point F)
    (firstRows : DoubleEquations (model.coordinates acc) first)
    (secondRows : DoubleEquations first second)
    (addRows : AddEquations d second
      (windowPoint (if low then 1 else 0) (if high then 1 else 0)
        (model.coordinates base) (model.coordinates (2 • base))
        (model.coordinates (3 • base))) output) :
    output = model.coordinates (4 • acc + (low.toNat + 2 * high.toNat) • base) := by
  have firstEqual := double_coordinates d imaginary model nonSquare imaginarySquare
    acc first firstRows.1 firstRows.2
  rw [firstEqual] at secondRows
  have secondEqual := double_coordinates d imaginary model nonSquare imaginarySquare
    (2 • acc) second secondRows.1 secondRows.2
  rw [secondEqual, selected_coordinates d model base low high] at addRows
  have result := add_coordinates d imaginary model nonSquare imaginarySquare
    (2 • (2 • acc)) ((low.toNat + 2 * high.toNat) • base) output addRows.1 addRows.2
  simpa only [← mul_nsmul] using result

theorem precompute_coordinates {F J : Type} [Field F] [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (base : J) (twice triple : Point F)
    (doubleRows : DoubleEquations (model.coordinates base) twice)
    (addRows : AddEquations d twice (model.coordinates base) triple) :
    twice = model.coordinates (2 • base) ∧ triple = model.coordinates (3 • base) := by
  have twiceEqual := double_coordinates d imaginary model nonSquare imaginarySquare
    base twice doubleRows.1 doubleRows.2
  rw [twiceEqual] at addRows
  have tripleEqual := add_coordinates d imaginary model nonSquare imaginarySquare
    (2 • base) base triple addRows.1 addRows.2
  have count : 2 • base + base = 3 • base := by
    simp only [show (3 : Nat) = 2 + 1 from rfl, add_nsmul, one_nsmul]
  exact ⟨twiceEqual, tripleEqual.trans (congrArg model.coordinates count)⟩

structure WindowWitness (F : Type) where
  low : Bool
  high : Bool
  first : Point F
  second : Point F
  output : Point F

def WindowEquations {F : Type} [Field F] (d : F) (base twice triple input : Point F)
    (window : WindowWitness F) : Prop :=
  DoubleEquations input window.first ∧ DoubleEquations window.first window.second ∧
  AddEquations d window.second
    (windowPoint (if window.low then 1 else 0) (if window.high then 1 else 0)
      base twice triple) window.output

def TraceEquations {F : Type} [Field F] (d : F) (base twice triple : Point F) :
    Point F → List (WindowWitness F) → Prop
  | _, [] => True
  | input, window :: tail => WindowEquations d base twice triple input window ∧
      TraceEquations d base twice triple window.output tail

def traceOutput {F : Type} : Point F → List (WindowWitness F) → Point F
  | input, [] => input
  | _, window :: tail => traceOutput window.output tail

theorem trace_output_append {F : Type} (input : Point F)
    (left right : List (WindowWitness F)) :
    traceOutput input (left ++ right) = traceOutput (traceOutput input left) right := by
  induction left generalizing input with
  | nil => rfl
  | cons window tail ih =>
      exact ih window.output

theorem trace_equations_append {F : Type} [Field F] (d : F)
    (base twice triple input : Point F) (left right : List (WindowWitness F)) :
    TraceEquations d base twice triple input (left ++ right) ↔
      TraceEquations d base twice triple input left ∧
        TraceEquations d base twice triple (traceOutput input left) right := by
  induction left generalizing input with
  | nil => simp only [List.nil_append, TraceEquations, traceOutput, true_and]
  | cons window tail ih =>
      simp only [List.cons_append, TraceEquations, traceOutput, ih, and_assoc]

/-- Symbolic loop composition carries curve validity through the represented
accumulator. Precomputed point roles are established once by their equations. -/
theorem trace_coordinates {F J : Type} [Field F] [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (base : J) (twice triple : Point F)
    (doubleRows : DoubleEquations (model.coordinates base) twice)
    (addRows : AddEquations d twice (model.coordinates base) triple)
    (acc : J) (windows : List (WindowWitness F))
    (equations : TraceEquations d (model.coordinates base) twice triple
      (model.coordinates acc) windows) :
    traceOutput (model.coordinates acc) windows = model.coordinates
      (windows.foldl (fun current window =>
        4 • current + (window.low.toNat + 2 * window.high.toNat) • base) acc) := by
  obtain ⟨twiceEqual, tripleEqual⟩ := precompute_coordinates d imaginary model
    nonSquare imaginarySquare base twice triple doubleRows addRows
  rw [twiceEqual, tripleEqual] at equations
  induction windows generalizing acc with
  | nil => rfl
  | cons window tail ih =>
    have step := window_coordinates d imaginary model nonSquare imaginarySquare
      acc base window.low window.high window.first window.second window.output
      equations.1.1 equations.1.2.1 equations.1.2.2
    have remaining := equations.2
    rw [step] at remaining
    simpa only [traceOutput, List.foldl_cons, step] using ih _ remaining

/-- Iterator/bit-list correspondence is explicit. The circuit's actual Boolean
rows and source roles must supply the particular windows and little-endian bits. -/
theorem trace_scalar_coordinates {F J : Type} [Field F] [AddCommGroup J]
    (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary * imaginary = -1) (base : J) (twice triple : Point F)
    (doubleRows : DoubleEquations (model.coordinates base) twice)
    (addRows : AddEquations d twice (model.coordinates base) triple)
    (windows : List (WindowWitness F)) (bits : List Bool)
    (order : windows.map (fun window => window.low.toNat + 2 * window.high.toNat) =
      (TransferWindows.pairDigits bits).reverse)
    (equations : TraceEquations d (model.coordinates base) twice triple
      (model.coordinates 0) windows) :
    traceOutput (model.coordinates 0) windows =
      model.coordinates (ShielddSecurity.binary bits • base) := by
  have trace := trace_coordinates d imaginary model nonSquare imaginarySquare
    base twice triple doubleRows addRows 0 windows equations
  have mapped : windows.foldl (fun current window =>
      4 • current + (window.low.toNat + 2 * window.high.toNat) • base) 0 =
      (windows.map (fun window => window.low.toNat + 2 * window.high.toNat)).foldl
        (fun current digit => 4 • current + digit • base) 0 := by
    simp only [List.foldl_map]
  rw [mapped, order, TransferWindows.variable_loop, TransferWindows.variable_value,
    TransferWindows.pair_digits_value] at trace
  exact trace

set_option pp.all true in
#check @double_coordinates
#print axioms double_coordinates
set_option pp.all true in
#check @add_coordinates
#print axioms add_coordinates
set_option pp.all true in
#check @selected_coordinates
#print axioms selected_coordinates
set_option pp.all true in
#check @window_coordinates
#print axioms window_coordinates
set_option pp.all true in
#check @precompute_coordinates
#print axioms precompute_coordinates
set_option pp.all true in
#check @trace_coordinates
#print axioms trace_coordinates
set_option pp.all true in
#check @trace_scalar_coordinates
#print axioms trace_scalar_coordinates
set_option pp.all true in
#check @trace_output_append
#print axioms trace_output_append
set_option pp.all true in
#check @trace_equations_append
#print axioms trace_equations_append

end ShielddSecurity.TransferOwnership
