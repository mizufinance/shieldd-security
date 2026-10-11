from pathlib import Path
import json,hashlib,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-registry-point-semantic200-source01'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');require(not S.exists(),'immutable source')
body='''import ShielddSecurity.CapturedSubgroupModel199
import ShielddSecurity.RegistryRecovery194
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryPointSemantic200
open PoseidonNatural192
variable {F J : Type} [Field F] [AddCommGroup J]
def encode (representation : CanonicalRepresentation F) (point : Group.Point F) : TransferCore.Affine :=
 ⟨representation.value point.x,representation.value point.y⟩
def interpret (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 {d : F} (model : Group.StandardCurveModel J d) : TransferSem.Crypto :=
 {c with subgroup:=fun point => ∃ represented : J,
   encode representation (model.coordinates represented)=point ∧ TransferCore.scalarOrder • represented=0}
theorem valid_of_member (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 {d : F} (model : Group.StandardCurveModel J d) (point : Group.Point F)
 (member : CapturedSubgroupModel199.Member model point) :
 TransferSem.ValidPoint (interpret c representation model) (encode representation point) := by
 rcases member with ⟨represented,coordinates,killed⟩
 refine ⟨⟨representation.bounded _,representation.bounded _⟩,represented,?_,killed⟩
 exact congrArg (encode representation) coordinates
variable [CharP F TransferFirstSubgroupData01.p]
theorem registry_points (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 (rho : Nat → F) (one : rho 0=1)
 (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F))
 (standardOrder : ∀ point : J,(8*TransferCore.scalarOrder) • point=0) :
 TransferSem.ValidPoint (interpret c representation model) (RegistryRecovery194.recover representation rho).detection ∧
 TransferSem.ValidPoint (interpret c representation model) (RegistryRecovery194.recover representation rho).ring ∧
 TransferSem.ValidPoint (interpret c representation model) (RegistryRecovery194.recover representation rho).audit.payload ∧
 TransferSem.ValidPoint (interpret c representation model) (RegistryRecovery194.recover representation rho).audit.checking := by
 rcases CapturedSubgroupModel199.captured_four rho one satisfied imaginary nonSquare imaginarySquare model standardOrder with ⟨a,b,c,d⟩
 exact ⟨valid_of_member _ representation model _ a,valid_of_member _ representation model _ b,
   valid_of_member _ representation model _ c,valid_of_member _ representation model _ d⟩
end ShielddSecurity.RegistryPointSemantic200
'''
pins=[W/'mac-captured-subgroup-model199-source02/source-root/ShielddSecurity/CapturedSubgroupModel199.lean',W/'mac-registry-recovery194-source01/source-root/ShielddSecurity/RegistryRecovery194.lean',W/'shared-build-handoff/handoffs/transfer-20261009/sources/windows/semantic-torsion-20261010-01/handwritten-source/ShielddSecurity/TransferSemanticSubgroup48.lean']
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes())
(S/'templates01.json').write_text(json.dumps(dict(modules={'RegistryPointSemantic200':dict(body=body,names=['encode','interpret','valid_of_member','registry_points'])},inputs={str(p):pin(p)for p in pins},scope='SOURCE_ONLY_UNRUN. Thin chosen mathematical subgroup interpretation uses exactly the encoded r-annihilated model-points predicate of existing SemanticSubgroup48 (decode/value and Scalar.order/Core.scalarOrder literal correspondence); no claim an existing native Crypto already has it. Full rows derive four recovered Registry ValidPoints with independent model/global exponent/coefficient certificates explicit. No desired validity or RegistrySem premise. Four planned reports; other Crypto fields unchanged.'),sort_keys=True,separators=(',',':'))+'\n')
