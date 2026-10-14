-- GENERATED from points.json by generate.py. Do not hand edit.
import ShielddSecurity.AuthorizationFixedDomain485
import ShielddSecurity.SubgroupNonidentity350
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedGeneratorSubgroup586
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
def preimage : Group.Point F := ⟨37683234540996304297355311881032003424807082249757251600096341828054461789857,27875887990706589449530982534182806288472263315094746115882028963250524979256⟩
def twice : Group.Point F := ⟨29916549470988916218589752428218325648280462885198257084357273626962374118918,26149085726079919735995544527779445212309601991788591142203830584072926355085⟩
def four : Group.Point F := ⟨23249289844844859093750636231077989443881353472704813104328905583301159137772,50996227070909932084078839410183976686567041008890020348918907690379918854605⟩
theorem preimage_onCurve : Group.OnCurve (CapturedFirstSubgroup81.d:F) preimage := by
  unfold Group.OnCurve
  decide +kernel

theorem first : twice=Group.affineAdd (CapturedFirstSubgroup81.d:F) preimage preimage := by
  apply congrArg₂ Group.Point.mk <;> decide +kernel
theorem second : four=Group.affineAdd (CapturedFirstSubgroup81.d:F) twice twice := by
  apply congrArg₂ Group.Point.mk <;> decide +kernel
theorem third : AuthorizationFixedDomain485.base=Group.affineAdd (CapturedFirstSubgroup81.d:F) four four := by
  apply congrArg₂ Group.Point.mk <;> decide +kernel

attribute [local irreducible] model

theorem base_member : CapturedSubgroupModel199.Member model AuthorizationFixedDomain485.base :=
  Group.cofactor_image_annihilated (CapturedFirstSubgroup81.d:F) model TransferCore.scalarOrder
    standard_order preimage twice four AuthorizationFixedDomain485.base preimage_onCurve first second third

theorem represented_subgroup : TransferCore.scalarOrder • AuthorizationFixedDomain485.represented=0 := by
  obtain ⟨point,coordinates,killed⟩ := base_member
  have equal : point=AuthorizationFixedDomain485.represented :=
    model.injective (coordinates.trans AuthorizationFixedDomain485.coordinates.symm)
  rw [equal] at killed
  exact killed

theorem multiple_member (scalar : Nat) :
    CapturedSubgroupModel199.Member model (model.coordinates (scalar • AuthorizationFixedDomain485.represented)) := by
  refine ⟨scalar • AuthorizationFixedDomain485.represented,rfl,?_⟩
  rw [←mul_nsmul,Nat.mul_comm,mul_nsmul,represented_subgroup,nsmul_zero]

end ShielddSecurity.CapturedGeneratorSubgroup586

set_option pp.all true in
#check @ShielddSecurity.CapturedGeneratorSubgroup586.preimage
#print axioms ShielddSecurity.CapturedGeneratorSubgroup586.preimage

set_option pp.all true in
#check @ShielddSecurity.CapturedGeneratorSubgroup586.twice
#print axioms ShielddSecurity.CapturedGeneratorSubgroup586.twice

set_option pp.all true in
#check @ShielddSecurity.CapturedGeneratorSubgroup586.four
#print axioms ShielddSecurity.CapturedGeneratorSubgroup586.four

set_option pp.all true in
#check @ShielddSecurity.CapturedGeneratorSubgroup586.preimage_onCurve
#print axioms ShielddSecurity.CapturedGeneratorSubgroup586.preimage_onCurve

set_option pp.all true in
#check @ShielddSecurity.CapturedGeneratorSubgroup586.first
#print axioms ShielddSecurity.CapturedGeneratorSubgroup586.first

set_option pp.all true in
#check @ShielddSecurity.CapturedGeneratorSubgroup586.second
#print axioms ShielddSecurity.CapturedGeneratorSubgroup586.second

set_option pp.all true in
#check @ShielddSecurity.CapturedGeneratorSubgroup586.third
#print axioms ShielddSecurity.CapturedGeneratorSubgroup586.third

set_option pp.all true in
#check @ShielddSecurity.CapturedGeneratorSubgroup586.base_member
#print axioms ShielddSecurity.CapturedGeneratorSubgroup586.base_member

set_option pp.all true in
#check @ShielddSecurity.CapturedGeneratorSubgroup586.represented_subgroup
#print axioms ShielddSecurity.CapturedGeneratorSubgroup586.represented_subgroup

set_option pp.all true in
#check @ShielddSecurity.CapturedGeneratorSubgroup586.multiple_member
#print axioms ShielddSecurity.CapturedGeneratorSubgroup586.multiple_member
