import ShielddSecurity.FixedFamilyJoin543
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.FixedFamilySound577
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
open VariableWindowColumns449 (columnPoint)
attribute [local irreducible] model

theorem output (rho : Nat → F) (acc : curve.Point) (low high : Bool)
    (layout : FixedFamilyJoin543.Layout) (entry : FixedFamilyJoin543.Entry)
    (checked : FixedFamilyJoin543.check layout entry=true) (matched : FixedWindowMeaning491.check entry=true)
    (one : rho copy=1) (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (previousMeaning : columnPoint rho (layout.points+2*(entry.index-1))=model.coordinates acc)
    (lowMeaning : rho (layout.bits+2*entry.index)=if low then 1 else 0)
    (highMeaning : rho (layout.bits+2*entry.index+1)=if high then 1 else 0)
    (satisfied : VariableOperationAdapter434.Rows rho entry.operation) :
    columnPoint rho (layout.points+2*entry.index)=
      model.coordinates (acc+(low.toNat+2*high.toNat) • (4^entry.index • AuthorizationFixedDomain485.represented)) := by
  have valid : FixedFamilyJoin543.Valid layout entry := of_decide_eq_true checked
  have upper := valid.2.2.2.2.1
  have equations := (FixedFamilyJoin543.rows_iff layout entry checked rho one arithmetic).mp satisfied
  have points := FixedWindowMeaning491.points entry matched
  have table := AuthorizationFixedTables490.table_coordinates entry.index upper
  rw [previousMeaning,lowMeaning,highMeaning,points.1,points.2.1,points.2.2,
    AuthorizationFixedTables490.base_coordinates entry.index upper,table.1,table.2.1,
    TransferOwnership.selected_coordinates (CapturedFirstSubgroup81.d:F) model _ low high] at equations
  exact TransferOwnership.add_coordinates (CapturedFirstSubgroup81.d:F) imaginary model
    (by rw [coefficient_eq];exact ConcreteJubjubField01.coefficient_no_unit_square)
    imaginary_square _ _ _ equations.1 equations.2
end ShielddSecurity.FixedFamilySound577
set_option pp.all true in
#check @ShielddSecurity.FixedFamilySound577.output
#print axioms ShielddSecurity.FixedFamilySound577.output
