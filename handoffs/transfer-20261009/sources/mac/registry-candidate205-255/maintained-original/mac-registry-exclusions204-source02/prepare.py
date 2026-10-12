from pathlib import Path
import sys,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-registry-exclusions204-source02'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags');require(not S.exists(),'immutable source')
body='''import ShielddSecurity.RegistryRecovery194
import ShielddSecurity.CapturedRegistryPointDomain75
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryExclusions204
open PoseidonNatural192 RegistryRecovery194 CapturedRegistryPointDomain75
open CompilerArithmeticTransport41 (p)
variable {F : Type} [Field F] [CharP F p]
'''
names=[]
for i,(name,left,right,xl,yl,xr,yr) in enumerate([
 ('payload_identity','(recover representation rho).audit.payload','(⟨0,1⟩ : TransferCore.Affine)',35,36,'(0:Nat)','(1:Nat)'),
 ('payload_sink','(recover representation rho).audit.payload','sink',35,36,'sink.x','sink.y'),
 ('payload_checking','(recover representation rho).audit.payload','(recover representation rho).audit.checking',35,36,'representation.value (rho 42)','representation.value (rho 43)'),
 ('checking_identity','(recover representation rho).audit.checking','(⟨0,1⟩ : TransferCore.Affine)',42,43,'(0:Nat)','(1:Nat)'),
 ('checking_sink','(recover representation rho).audit.checking','sink',42,43,'sink.x','sink.y')]):
 names.append(name)
 body+=f'''theorem {name} (representation : CanonicalRepresentation F) (rho : Nat → F)
 (one : rho 0=1) (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (regulated : rho 10≠0) : {left}≠{right} := by
 intro same
 have hx:=congrArg (fun point : TransferCore.Affine => (point.x:F)) same
 have hy:=congrArg (fun point : TransferCore.Affine => (point.y:F)) same
 change (representation.value (rho {xl}):F)=({xr}:F) at hx
 change (representation.value (rho {yl}):F)=({yr}:F) at hy
 simp only [representation.cast_value] at hx hy
 apply regulated
 apply CapturedGlobalRegistered74.full_forbidden_pair rho one satisfied {i} (by decide)
 constructor
 · rw [meaning_value rho {2*i} (by decide)]
   norm_num [meaningTerms,eval,one,hx,sink]
 · rw [meaning_value rho {2*i+1} (by decide)]
   norm_num [meaningTerms,eval,one,hy,sink]
'''
body+='''theorem all_guards (representation : CanonicalRepresentation F) (rho : Nat → F)
 (one : rho 0=1) (satisfied : CompilerAssertionBlock51.SatisfiesAt rho CapturedFullRelation58.rowAt 200770)
 (regulated : rho 10≠0) :
 (recover representation rho).audit.payload≠⟨0,1⟩ ∧
 (recover representation rho).audit.checking≠⟨0,1⟩ ∧
 (recover representation rho).audit.payload≠sink ∧
 (recover representation rho).audit.checking≠sink ∧
 (recover representation rho).audit.payload≠(recover representation rho).audit.checking :=
 ⟨payload_identity representation rho one satisfied regulated,
 checking_identity representation rho one satisfied regulated,
 payload_sink representation rho one satisfied regulated,
 checking_sink representation rho one satisfied regulated,
 payload_checking representation rho one satisfied regulated⟩
end ShielddSecurity.RegistryExclusions204
''';names.append('all_guards')
pins=[W/'mac-registry-exclusions204-source01/producer-manifest01.json',W/'mac-registry-recovery194-source01/source-root/ShielddSecurity/RegistryRecovery194.lean',W/'mac-registry-point-domain75-source04/source-root/ShielddSecurity/CapturedRegistryPointDomain75.lean']
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes())
(S/'templates01.json').write_text(json.dumps(dict(modules={'RegistryExclusions204':dict(body=body,names=names)},inputs={str(p):pin(p)for p in pins},scope='SOURCE_ONLY_UNRUN. Full actual captured relation and rho0=1 derive regulated five natural-coordinate exclusions through qualified forbidden-pair rows; no desired semantic exclusion or target-truth premise. Six planned reports; no global semantic/native conclusion.'),sort_keys=True,separators=(',',':'))+'\n')
