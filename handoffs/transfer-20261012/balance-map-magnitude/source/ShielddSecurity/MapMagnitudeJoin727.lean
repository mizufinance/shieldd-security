import ShielddSecurity.MapAssignmentValues720
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapMagnitudeJoin727
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open MapAssignmentValues720
attribute [local irreducible] assignment model ConcreteCofactorModel01.model

theorem point_columns (rho : Nat → F) :
    VariableWindowJoin443.point rho [(190237,1)] [(190241,1)]=Group.Point.mk (rho 190237) (rho 190241) := by
  simp only [VariableWindowJoin443.point,eval,Int.cast_one,one_mul,add_zero]

set_option pp.all true in
#check @ShielddSecurity.MapMagnitudeJoin727.point_columns
#print axioms ShielddSecurity.MapMagnitudeJoin727.point_columns

noncomputable def BaseMeaning (rho : Nat → F) (u : F) : Prop :=
  VariableWindowJoin443.point rho [(190237,1)] [(190241,1)]=model.coordinates (BalanceMapPoint701.represented u)

set_option pp.all true in
#check @ShielddSecurity.MapMagnitudeJoin727.BaseMeaning
#print axioms ShielddSecurity.MapMagnitudeJoin727.BaseMeaning

theorem coordinates_from_values (rho : Nat → F) (u : F)
    (meaning : MapCofactorJoin714.Values rho u)
    (satisfied : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    BaseMeaning rho u :=
  (point_columns rho).trans ((MapCofactorJoin714.base_coordinates rho u meaning satisfied).trans
    (model_coordinates (BalanceMapPoint701.represented u)).symm)

set_option pp.all true in
#check @ShielddSecurity.MapMagnitudeJoin727.coordinates_from_values
#print axioms ShielddSecurity.MapMagnitudeJoin727.coordinates_from_values

end ShielddSecurity.MapMagnitudeJoin727
