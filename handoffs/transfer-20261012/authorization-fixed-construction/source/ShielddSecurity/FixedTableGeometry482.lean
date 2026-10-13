import ShielddSecurity.FixedTraceConstruction478
import ShielddSecurity.FixedSelectorAdapter480
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedTableGeometry482
open Group TransferOwnership
variable {F J : Type} [Field F] [AddCommGroup J]
def Equations (d : F) (base twice triple next : Point F) : Prop :=
  OnCurve d base ∧ AddEquations d base base twice ∧
  AddEquations d twice base triple ∧ AddEquations d twice twice next
noncomputable instance equationsDecidable [DecidableEq F] (d : F) (base twice triple next : Point F) :
    Decidable (Equations d base twice triple next) := by
  unfold Equations OnCurve AddEquations
  infer_instance

theorem coordinates (d imaginary : F) (model : StandardCurveModel J d) (nonSquare : NoUnitSquare d)
    (imaginarySquare : imaginary*imaginary = -1) (represented : J) (base twice triple next : Point F)
    (known : model.coordinates represented=base) (equations : Equations d base twice triple next) :
    twice=model.coordinates (2 • represented) ∧ triple=model.coordinates (3 • represented) ∧
    next=model.coordinates (4 • represented) := by
  have first := equations.2.1
  rw [←known] at first
  have twiceEqual := add_coordinates d imaginary model nonSquare imaginarySquare represented represented twice first.1 first.2
  have twiceCount : represented+represented=2 • represented := (two_nsmul represented).symm
  rw [twiceCount] at twiceEqual
  have second := equations.2.2.1
  rw [←known,twiceEqual] at second
  have tripleEqual := add_coordinates d imaginary model nonSquare imaginarySquare (2 • represented) represented triple second.1 second.2
  have tripleCount : 2 • represented+represented=3 • represented := by
    simp only [show (3:Nat)=2+1 from rfl,add_nsmul,one_nsmul]
  rw [tripleCount] at tripleEqual
  have third := equations.2.2.2
  rw [twiceEqual] at third
  have nextEqual := add_coordinates d imaginary model nonSquare imaginarySquare (2 • represented) (2 • represented) next third.1 third.2
  have fourCount : 2 • represented+2 • represented=4 • represented := by rw [←add_nsmul]
  rw [fourCount] at nextEqual
  exact ⟨twiceEqual,tripleEqual,nextEqual⟩

theorem representation (d : F) (model : StandardCurveModel J d) (base twice triple next : Point F)
    (equations : Equations d base twice triple next) : ∃ represented,model.coordinates represented=base :=
  model.covers base equations.1
end ShielddSecurity.FixedTableGeometry482

set_option pp.all true in
#check @ShielddSecurity.FixedTableGeometry482.Equations
#print axioms ShielddSecurity.FixedTableGeometry482.Equations

set_option pp.all true in
#check @ShielddSecurity.FixedTableGeometry482.coordinates
#print axioms ShielddSecurity.FixedTableGeometry482.coordinates

set_option pp.all true in
#check @ShielddSecurity.FixedTableGeometry482.representation
#print axioms ShielddSecurity.FixedTableGeometry482.representation
