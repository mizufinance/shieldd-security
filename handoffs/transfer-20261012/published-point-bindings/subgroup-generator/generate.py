from pathlib import Path
import json,argparse,os,hashlib
root=Path(__file__).resolve().parent;ap=argparse.ArgumentParser();ap.add_argument('output',type=Path);a=ap.parse_args();assert not a.output.exists();out=a.output.with_name(a.output.name+'.pending');dest=out/'source-root/ShielddSecurity';dest.mkdir(parents=True);data=json.loads((root/'points.json').read_text())
s='''-- GENERATED from points.json by generate.py. Do not hand edit.
import ShielddSecurity.AuthorizationFixedDomain485
import ShielddSecurity.SubgroupNonidentity350
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedGeneratorSubgroup586
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294
'''
for name in ['preimage','twice','four']:s+=f'def {name} : Group.Point F := ⟨{data[name][0]},{data[name][1]}⟩\n'
s+='''theorem preimage_onCurve : Group.OnCurve (CapturedFirstSubgroup81.d:F) preimage := by
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
'''
names=['preimage','twice','four','preimage_onCurve','first','second','third','base_member','represented_subgroup','multiple_member']
for n in names:s+='\nset_option pp.all true in\n#check @ShielddSecurity.CapturedGeneratorSubgroup586.'+n+'\n#print axioms ShielddSecurity.CapturedGeneratorSubgroup586.'+n+'\n'
p=dest/'CapturedGeneratorSubgroup586.lean';p.write_text(s);(out/'generation.json').write_text(json.dumps({'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'audits':names,'native_credit':0},indent=2)+'\n');os.replace(out,a.output);print('Generated explicit cofactor-preimage certificate; unrun')
