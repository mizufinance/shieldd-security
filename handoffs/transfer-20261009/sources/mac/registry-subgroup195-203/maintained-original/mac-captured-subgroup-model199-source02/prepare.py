from pathlib import Path
import json,hashlib,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-captured-subgroup-model199-source02'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');require(not S.exists(),'immutable source')
body='''import ShielddSecurity.TransferCore
import ShielddSecurity.GroupWindows
import ShielddSecurity.CompilerSubgroupClosure83
import ShielddSecurity.CapturedFourSubgroups82
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedSubgroupModel199
open CompilerSubgroupArithmetic79
variable {F J : Type} [Field F] [AddCommGroup J]
def Member {d : F} (model : Group.StandardCurveModel J d) (point : Group.Point F) : Prop :=
 ∃ represented : J,model.coordinates represented=point ∧ TransferCore.scalarOrder • represented=0
theorem double_affine (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
 (imaginarySquare : imaginary*imaginary = -1) (point : Group.Point F)
 (valid : Group.OnCurve d point) : double d point=Group.affineAdd d point point := by
 have inverseRow : inverseProduct d point*(inverseProduct d point)⁻¹=1 :=
   mul_inv_cancel₀ (CompilerSubgroupClosure83.inverse_nonzero d imaginary nonSquare imaginarySquare point valid)
 exact (Group.shared_inverse_double_sound d imaginary (inverseProduct d point)⁻¹
   nonSquare imaginarySquare point (double d point) valid inverseRow rfl rfl).1
theorem trace_affine (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
 (imaginarySquare : imaginary*imaginary = -1) (point : Group.Point F)
 (valid : Group.OnCurve d point) (count : Nat) :
 trace d point (count+1)=Group.affineAdd d (trace d point count) (trace d point count) :=
 double_affine d imaginary nonSquare imaginarySquare _
   (CompilerSubgroupClosure83.trace_curve d imaginary nonSquare imaginarySquare point valid count)
theorem cofactor (d imaginary : F) (nonSquare : Group.NoUnitSquare d)
 (imaginarySquare : imaginary*imaginary = -1) (model : Group.StandardCurveModel J d)
 (standardOrder : ∀ point : J,(8*TransferCore.scalarOrder) • point=0)
 (point : Group.Point F) (valid : Group.OnCurve d point) : Member model (eight d point) := by
 apply Group.cofactor_image_annihilated d model TransferCore.scalarOrder standardOrder point
   (trace d point 1) (trace d point 2) (eight d point) valid
 · exact trace_affine d imaginary nonSquare imaginarySquare point valid 0
 · exact trace_affine d imaginary nonSquare imaginarySquare point valid 1
 · exact trace_affine d imaginary nonSquare imaginarySquare point valid 2
variable [CharP F TransferFirstSubgroupData01.p]
theorem captured_four (rho : Nat → F) (one : rho 0=1)
 (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F))
 (standardOrder : ∀ point : J,(8*TransferCore.scalarOrder) • point=0) :
 Member model ⟨rho 14,rho 15⟩ ∧ Member model ⟨rho 23,rho 24⟩ ∧
 Member model ⟨rho 35,rho 36⟩ ∧ Member model ⟨rho 42,rho 43⟩ := by
 rcases CapturedFourSubgroups82.all_four rho one satisfied with ⟨a,b,c,d⟩
 constructor
 · rw [←a.2]
   exact cofactor _ imaginary nonSquare imaginarySquare model standardOrder _ a.1
 constructor
 · rw [←b.2]
   exact cofactor _ imaginary nonSquare imaginarySquare model standardOrder _ b.1
 constructor
 · rw [←c.2]
   exact cofactor _ imaginary nonSquare imaginarySquare model standardOrder _ c.1
 · rw [←d.2]
   exact cofactor _ imaginary nonSquare imaginarySquare model standardOrder _ d.1
end ShielddSecurity.CapturedSubgroupModel199
'''
pins=[W/'mac-group-windows198-source01/source-root/ShielddSecurity/GroupWindows.lean',W/'mac-subgroup-closure83-source02/source-root/ShielddSecurity/CompilerSubgroupClosure83.lean',W/'mac-four-subgroups82-source05/source-root/ShielddSecurity/CapturedFourSubgroups82.lean',W/'mac-registry-epoch-semantic66-source02/source-root/ShielddSecurity/TransferCore.lean',W/'mac-captured-subgroup-model199-source01/producer-manifest01.json']
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes())
(S/'templates01.json').write_text(json.dumps(dict(modules={'CapturedSubgroupModel199':dict(body=body,names=['Member','double_affine','trace_affine','cofactor','captured_four'])},inputs={str(p):pin(p)for p in pins},scope='SOURCE_ONLY_UNRUN. Full captured relation derives all four original point representations in the r-annihilated subgroup of an explicitly chosen StandardCurveModel. Independent universal8r exponent and actual coefficient nonsquare/imaginary-square certificates are explicit; no claimed-point validity, preimage existence, native or Transfer conclusion assumed. Five planned reports unrun; concrete desktop premises not fresh Mac qualification.'),sort_keys=True,separators=(',',':'))+'\n')
