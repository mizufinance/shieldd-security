import ShielddSecurity.AuthorizationTraceSeed451
import ShielddSecurity.VariableTraceAccess452
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationTraceLocal453
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open AuthorizationTraceIndex450 AuthorizationTraceSeed451

theorem trace_length (base : curve.Point) (scalar : Nat) : (trace base scalar).length=126 := by
  simp [trace,VariableTraceBits446.windows_length]

theorem window_equations (base : curve.Point) (scalar window : Nat) (bound : window<126) :
    TransferOwnership.WindowEquations (CapturedFirstSubgroup81.d:F)
      (model.coordinates base) (model.coordinates (2 • base)) (model.coordinates (3 • base))
      (VariableTraceAccess452.before (model.coordinates 0) (trace base scalar) empty window)
      (windowAt base scalar window) := by
  apply VariableTraceAccess452.indexed_equations
  · simpa only [trace_length] using bound
  · exact VariableTraceBits446.equations (CapturedFirstSubgroup81.d:F) ConcreteJubjubField01.imaginary model
      (by rw [coefficient_eq];exact ConcreteJubjubField01.coefficient_no_unit_square)
      ConcreteJubjubField01.imaginary_square base (encodeBits 252 scalar)

theorem before_positive (base : curve.Point) (scalar window : Nat) (lower : 1≤window) :
    VariableTraceAccess452.before (model.coordinates 0) (trace base scalar) empty window=
      (windowAt base scalar (window-1)).output := by
  cases window with
  | zero => omega
  | succ index => rfl

theorem previous_point (original : Nat → F) (bases : Nat → curve.Point) (scalar family window : Nat)
    (familyBound : family<2) (lower : 1≤window) (upper : window<126) :
    VariableWindowColumns449.columnPoint (seed original bases scalar) (column family (window-1) 2 0)=
      VariableTraceAccess452.before (model.coordinates 0) (trace (bases family) scalar) empty window := by
  by_cases first : window=1
  · subst window
    rw [prefix_point original bases scalar family 2 familyBound (by decide)]
    rfl
  · rw [window_point original bases scalar family (window-1) 2 familyBound (by omega) (by omega) (by decide),
      before_positive (bases family) scalar window lower]
    rfl

def hintWindow (original : Nat → F) (bases : Nat → curve.Point) (scalar family window : Nat) :
    TransferOwnership.WindowWitness F :=
  ⟨(windowAt (bases family) scalar window).low,(windowAt (bases family) scalar window).high,
    VariableWindowColumns449.columnPoint (seed original bases scalar) (column family window 0 0),
    VariableWindowColumns449.columnPoint (seed original bases scalar) (column family window 1 0),
    VariableWindowColumns449.columnPoint (seed original bases scalar) (column family window 2 0)⟩

theorem hint_window (original : Nat → F) (bases : Nat → curve.Point) (scalar family window : Nat)
    (familyBound : family<2) (lower : 1≤window) (upper : window<126) :
    hintWindow original bases scalar family window=windowAt (bases family) scalar window := by
  unfold hintWindow
  rw [window_point original bases scalar family window 0 familyBound lower upper (by decide),
    window_point original bases scalar family window 1 familyBound lower upper (by decide),
    window_point original bases scalar family window 2 familyBound lower upper (by decide)]
  rfl

theorem seed_equations (original : Nat → F) (bases : Nat → curve.Point) (scalar family window : Nat)
    (familyBound : family<2) (lower : 1≤window) (upper : window<126) :
    TransferOwnership.WindowEquations (CapturedFirstSubgroup81.d:F) (model.coordinates (bases family))
      (VariableWindowColumns449.columnPoint (seed original bases scalar) (column family 0 0 0))
      (VariableWindowColumns449.columnPoint (seed original bases scalar) (column family 0 1 0))
      (VariableWindowColumns449.columnPoint (seed original bases scalar) (column family (window-1) 2 0))
      (hintWindow original bases scalar family window) := by
  rw [prefix_point original bases scalar family 0 familyBound (by decide),
    prefix_point original bases scalar family 1 familyBound (by decide),
    previous_point original bases scalar family window familyBound lower upper,
    hint_window original bases scalar family window familyBound lower upper]
  exact window_equations (bases family) scalar window upper
end ShielddSecurity.AuthorizationTraceLocal453

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceLocal453.trace_length
#print axioms ShielddSecurity.AuthorizationTraceLocal453.trace_length

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceLocal453.window_equations
#print axioms ShielddSecurity.AuthorizationTraceLocal453.window_equations

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceLocal453.before_positive
#print axioms ShielddSecurity.AuthorizationTraceLocal453.before_positive

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceLocal453.previous_point
#print axioms ShielddSecurity.AuthorizationTraceLocal453.previous_point

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceLocal453.hintWindow
#print axioms ShielddSecurity.AuthorizationTraceLocal453.hintWindow

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceLocal453.hint_window
#print axioms ShielddSecurity.AuthorizationTraceLocal453.hint_window

set_option pp.all true in
#check @ShielddSecurity.AuthorizationTraceLocal453.seed_equations
#print axioms ShielddSecurity.AuthorizationTraceLocal453.seed_equations
