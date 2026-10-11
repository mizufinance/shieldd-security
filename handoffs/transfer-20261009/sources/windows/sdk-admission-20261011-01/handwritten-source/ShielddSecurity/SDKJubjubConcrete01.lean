import ShielddSecurity.SDKJubjubExtended01
import ShielddSecurity.ConcreteCofactorModel01

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.SDKJubjubConcrete01
open ShielddSecurity.SDKJubjubExtended01

theorem concrete_double (value : Extended ConcreteJubjubField01.F)
    (point : ConcretePointTorsion01.curve.Point)
    (represented : Represents value (ConcreteCofactorModel01.model.coordinates point)) :
    Represents (double value) (ConcreteCofactorModel01.model.coordinates (2 • point)) := by
  rw [two_nsmul, ConcreteCofactorModel01.model.addition]
  exact double_represents ConcreteJubjubField01.coefficient ConcreteJubjubField01.imaginary
    ConcreteJubjubField01.coefficient_no_unit_square ConcreteJubjubField01.imaginary_square
    value _ represented (ConcreteCofactorModel01.model.onCurve point)

theorem concrete_add (left right : Extended ConcreteJubjubField01.F)
    (p q : ConcretePointTorsion01.curve.Point)
    (leftRep : Represents left (ConcreteCofactorModel01.model.coordinates p))
    (rightRep : Represents right (ConcreteCofactorModel01.model.coordinates q)) :
    Represents (add ConcreteJubjubField01.coefficient left right)
      (ConcreteCofactorModel01.model.coordinates (p + q)) := by
  rw [ConcreteCofactorModel01.model.addition]
  exact add_represents ConcreteJubjubField01.coefficient ConcreteJubjubField01.imaginary
    ConcreteJubjubField01.coefficient_no_unit_square ConcreteJubjubField01.imaginary_square
    ConcreteJubjubField01.two_ne_zero left right _ _ leftRep rightRep
    (ConcreteCofactorModel01.model.onCurve p) (ConcreteCofactorModel01.model.onCurve q)

end ShielddSecurity.SDKJubjubConcrete01

set_option pp.all true in
#check @ShielddSecurity.SDKJubjubConcrete01.concrete_double
#print axioms ShielddSecurity.SDKJubjubConcrete01.concrete_double
set_option pp.all true in
#check @ShielddSecurity.SDKJubjubConcrete01.concrete_add
#print axioms ShielddSecurity.SDKJubjubConcrete01.concrete_add
