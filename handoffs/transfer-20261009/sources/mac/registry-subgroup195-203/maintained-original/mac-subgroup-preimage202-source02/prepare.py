from pathlib import Path
import json,hashlib,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-subgroup-preimage202-source02'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');require(not S.exists(),'immutable source')
body='''import ShielddSecurity.CapturedSubgroupModel199
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SubgroupPreimage202
open CompilerSubgroupArithmetic79
variable {F J : Type} [Field F] [AddCommGroup J]
def inverseEight : Nat := (TransferCore.scalarOrder+1)/8
theorem inverse_identity : 8*inverseEight=TransferCore.scalarOrder+1 := by
 unfold inverseEight TransferCore.scalarOrder
 decide +kernel
theorem pullback (point : J) (annihilated : TransferCore.scalarOrder • point=0) :
 (8:Nat) • (inverseEight • point)=point := by
 rw [←mul_nsmul,Nat.mul_comm inverseEight 8,inverse_identity,add_nsmul,annihilated,one_nsmul,zero_add]
theorem eight_coordinates (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
 (imaginarySquare : imaginary*imaginary = -1) (model : Group.StandardCurveModel J d)
 (point : J) : eight d (model.coordinates point)=model.coordinates ((8:Nat) • point) := by
 have valid:=model.onCurve point
 have first : model.coordinates (point+point)=trace d (model.coordinates point) 1 := by
   rw [model.addition]
   exact (CapturedSubgroupModel199.trace_affine d imaginary nonSquare imaginarySquare _ valid 0).symm
 have second : model.coordinates ((point+point)+(point+point))=trace d (model.coordinates point) 2 := by
   rw [model.addition,first]
   exact (CapturedSubgroupModel199.trace_affine d imaginary nonSquare imaginarySquare _ valid 1).symm
 have third : model.coordinates (((point+point)+(point+point))+((point+point)+(point+point)))=
   eight d (model.coordinates point) := by
   rw [model.addition,second]
   exact (CapturedSubgroupModel199.trace_affine d imaginary nonSquare imaginarySquare _ valid 2).symm
 have repeated : (((point+point)+(point+point))+((point+point)+(point+point)))=(8:Nat) • point := by
   simp only [←two_nsmul,←mul_nsmul]
 rw [repeated] at third
 exact third.symm
theorem member_preimage (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
 (imaginarySquare : imaginary*imaginary = -1) (model : Group.StandardCurveModel J d)
 (point : Group.Point F) (member : CapturedSubgroupModel199.Member model point) :
 ∃ preimage : Group.Point F,Group.OnCurve d preimage ∧ eight d preimage=point := by
 rcases member with ⟨represented,coordinates,annihilated⟩
 refine ⟨model.coordinates (inverseEight • represented),model.onCurve _,?_⟩
 rw [eight_coordinates d imaginary nonSquare imaginarySquare model,pullback represented annihilated]
 exact coordinates
end ShielddSecurity.SubgroupPreimage202
'''
pins=[W/'mac-subgroup-preimage202-source01/producer-manifest01.json',W/'mac-captured-subgroup-model199-source02/source-root/ShielddSecurity/CapturedSubgroupModel199.lean',W/'mac-registry-epoch-semantic66-source03/source-root/ShielddSecurity/TransferCore.lean']
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes())
(S/'templates01.json').write_text(json.dumps(dict(modules={'SubgroupPreimage202':dict(body=body,names=['inverseEight','inverse_identity','pullback','eight_coordinates','member_preimage'])},inputs={str(p):pin(p)for p in pins},scope='SOURCE_ONLY_UNRUN. Exact scalar r=7mod8 supports constructive preimage of every represented r-annihilated model point through inverse-eight nsmul. Field nonsquare/imaginary and exact model correspondence remain independent premises; no desired preimage or affine-doubling equation premise. Five planned standard-axiom/full-type reports; no SDK/native correspondence.'),sort_keys=True,separators=(',',':'))+'\n')
