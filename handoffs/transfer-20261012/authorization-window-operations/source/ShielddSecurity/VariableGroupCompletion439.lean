import ShielddSecurity.TransferOwnership
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VariableGroupCompletion439
open Group TransferOwnership
variable {F J : Type} [Field F] [AddCommGroup J]
variable (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
variable (imaginarySquare : imaginary*imaginary = -1)
include imaginary nonSquare imaginarySquare

theorem add_equations (left right : J) :
    AddEquations d (model.coordinates left) (model.coordinates right) (model.coordinates (left+right)) := by
  have nz := denominators_nonzero d imaginary nonSquare imaginarySquare
    (model.coordinates left) (model.coordinates right) (model.onCurve left) (model.onCurve right)
  unfold AddEquations
  rw [model.addition]
  simp only [affineAdd,div_mul_cancel₀ _ nz.1,div_mul_cancel₀ _ nz.2]
  constructor
  · unfold cross;ring
  · rfl

theorem double_equations (point : J) :
    DoubleEquations (model.coordinates point) (model.coordinates (2 • point)) := by
  have add := add_equations d imaginary model nonSquare imaginarySquare point point
  have plus : (model.coordinates point).y*(model.coordinates point).y-
      (model.coordinates point).x*(model.coordinates point).x = 1+delta d (model.coordinates point) (model.coordinates point) := model.onCurve point
  have minus : 2-((model.coordinates point).y*(model.coordinates point).y-
      (model.coordinates point).x*(model.coordinates point).x) = 1-delta d (model.coordinates point) (model.coordinates point) := by rw [plus];ring
  unfold DoubleEquations
  rw [two_nsmul]
  constructor
  · rw [plus]; exact add.1
  · rw [minus]; exact add.2

theorem add_iff (left right : J) (output : Point F) :
    AddEquations d (model.coordinates left) (model.coordinates right) output ↔
    output=model.coordinates (left+right) := by
  constructor
  · intro rows
    exact add_coordinates d imaginary model nonSquare imaginarySquare left right output rows.1 rows.2
  · intro equal
    rw [equal]
    exact add_equations d imaginary model nonSquare imaginarySquare left right

theorem double_iff (point : J) (output : Point F) :
    DoubleEquations (model.coordinates point) output ↔ output=model.coordinates (2 • point) := by
  constructor
  · intro rows
    exact double_coordinates d imaginary model nonSquare imaginarySquare point output rows.1 rows.2
  · intro equal
    rw [equal]
    exact double_equations d imaginary model nonSquare imaginarySquare point
end ShielddSecurity.VariableGroupCompletion439

set_option pp.all true in
#check @ShielddSecurity.VariableGroupCompletion439.add_equations
#print axioms ShielddSecurity.VariableGroupCompletion439.add_equations

set_option pp.all true in
#check @ShielddSecurity.VariableGroupCompletion439.double_equations
#print axioms ShielddSecurity.VariableGroupCompletion439.double_equations

set_option pp.all true in
#check @ShielddSecurity.VariableGroupCompletion439.add_iff
#print axioms ShielddSecurity.VariableGroupCompletion439.add_iff

set_option pp.all true in
#check @ShielddSecurity.VariableGroupCompletion439.double_iff
#print axioms ShielddSecurity.VariableGroupCompletion439.double_iff
