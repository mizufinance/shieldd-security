-- GENERATED from points.json by generate.py. Do not hand edit.
import ShielddSecurity.BalanceBlindingDomain670
import ShielddSecurity.SubgroupNonidentity350
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedBlindingSubgroup671
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
noncomputable def preimage : Group.Point F := ⟨22699659283203892130901583778207378433642196434108400836561818850230241435116,50707083985487567576243581187890909294849027544322534811572033751128394778485⟩
noncomputable def twice : Group.Point F := ⟨1561525641008388830947886671647483473959104631942342299533545038283817390269,17723139078264538383369654316200176126185494135952670137108359635013644053469⟩
noncomputable def four : Group.Point F := ⟨13732165223785839217583638971566442513794358207731562207135018882679150331442,18214609437879366511237467200430485888717984825927508725536348300114271034988⟩
theorem preimage_onCurve : Group.OnCurve (CapturedFirstSubgroup81.d:F) preimage := by
  unfold Group.OnCurve
  decide +kernel

theorem first : twice=Group.affineAdd (CapturedFirstSubgroup81.d:F) preimage preimage := by
  apply congrArg₂ Group.Point.mk <;> decide +kernel
theorem second : four=Group.affineAdd (CapturedFirstSubgroup81.d:F) twice twice := by
  apply congrArg₂ Group.Point.mk <;> decide +kernel
theorem third : BalanceBlindingDomain670.base=Group.affineAdd (CapturedFirstSubgroup81.d:F) four four := by
  apply congrArg₂ Group.Point.mk <;> decide +kernel

attribute [local irreducible] model

theorem base_member : CapturedSubgroupModel199.Member model BalanceBlindingDomain670.base :=
  Group.cofactor_image_annihilated (CapturedFirstSubgroup81.d:F) model TransferCore.scalarOrder
    standard_order preimage twice four BalanceBlindingDomain670.base preimage_onCurve first second third

theorem represented_subgroup : TransferCore.scalarOrder • BalanceBlindingDomain670.represented=0 := by
  obtain ⟨point,coordinates,killed⟩ := base_member
  have equal : point=BalanceBlindingDomain670.represented :=
    model.injective (coordinates.trans BalanceBlindingDomain670.coordinates.symm)
  rw [equal] at killed
  exact killed

theorem multiple_member (scalar : Nat) :
    CapturedSubgroupModel199.Member model (model.coordinates (scalar • BalanceBlindingDomain670.represented)) := by
  refine ⟨scalar • BalanceBlindingDomain670.represented,rfl,?_⟩
  rw [←mul_nsmul,Nat.mul_comm,mul_nsmul,represented_subgroup,nsmul_zero]

end ShielddSecurity.CapturedBlindingSubgroup671

set_option pp.all true in
#check @ShielddSecurity.CapturedBlindingSubgroup671.preimage
#print axioms ShielddSecurity.CapturedBlindingSubgroup671.preimage

set_option pp.all true in
#check @ShielddSecurity.CapturedBlindingSubgroup671.twice
#print axioms ShielddSecurity.CapturedBlindingSubgroup671.twice

set_option pp.all true in
#check @ShielddSecurity.CapturedBlindingSubgroup671.four
#print axioms ShielddSecurity.CapturedBlindingSubgroup671.four

set_option pp.all true in
#check @ShielddSecurity.CapturedBlindingSubgroup671.preimage_onCurve
#print axioms ShielddSecurity.CapturedBlindingSubgroup671.preimage_onCurve

set_option pp.all true in
#check @ShielddSecurity.CapturedBlindingSubgroup671.first
#print axioms ShielddSecurity.CapturedBlindingSubgroup671.first

set_option pp.all true in
#check @ShielddSecurity.CapturedBlindingSubgroup671.second
#print axioms ShielddSecurity.CapturedBlindingSubgroup671.second

set_option pp.all true in
#check @ShielddSecurity.CapturedBlindingSubgroup671.third
#print axioms ShielddSecurity.CapturedBlindingSubgroup671.third

set_option pp.all true in
#check @ShielddSecurity.CapturedBlindingSubgroup671.base_member
#print axioms ShielddSecurity.CapturedBlindingSubgroup671.base_member

set_option pp.all true in
#check @ShielddSecurity.CapturedBlindingSubgroup671.represented_subgroup
#print axioms ShielddSecurity.CapturedBlindingSubgroup671.represented_subgroup

set_option pp.all true in
#check @ShielddSecurity.CapturedBlindingSubgroup671.multiple_member
#print axioms ShielddSecurity.CapturedBlindingSubgroup671.multiple_member
