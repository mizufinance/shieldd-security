from pathlib import Path
import sys,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-registry-recovery194-source01'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site and not sys.flags.optimize,'isolated')
require(not S.exists(),'fresh immutable source')
n='RegistryRecovery194'
b='''import ShielddSecurity.RegistryNatural193
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryRecovery194
variable {F : Type} [Field F]
open PoseidonNatural192
open CapturedInitial73419Generic01 (p)
def recover (representation : CanonicalRepresentation F) (rho : Nat → F) : TransferSem.AssetLeaf where
 value:=representation.value (rho 11)
 nextIndex:=representation.value (rho 12)
 nextValue:=representation.value (rho 13)
 detection:=⟨representation.value (rho 14),representation.value (rho 15)⟩
 dailyLimit:=representation.value (rho 21)
 routePolicy:=representation.value (rho 22)
 ring:=⟨representation.value (rho 23),representation.value (rho 24)⟩
 ringID:=representation.value (rho 30)
 policyID:=representation.value (rho 31)
 permission:=representation.value (rho 32)
 resource:=representation.value (rho 33)
 audit:=⟨representation.value (rho 34),
   ⟨representation.value (rho 35),representation.value (rho 36)⟩,
   ⟨representation.value (rho 42),representation.value (rho 43)⟩⟩
 position:=representation.value (rho 135)
 siblings:=fun level slot => representation.value (rho (136+3*level.val+slot.val))
theorem roles (representation : CanonicalRepresentation F) (rho : Nat → F) :
 RegistryNatural193.Roles rho (recover representation rho) := by
 constructor <;> exact (representation.cast_value _).symm
theorem position_cast (representation : CanonicalRepresentation F) (rho : Nat → F) :
 ((recover representation rho).position:F)=rho 135 := representation.cast_value _
theorem position_canonical (representation : CanonicalRepresentation F) (rho : Nat → F) :
 (recover representation rho).position<p := by
 exact representation.bounded _
theorem siblings_cast (representation : CanonicalRepresentation F) (rho : Nat → F)
 (level : Fin 16) (slot : Fin 3) :
 ((recover representation rho).siblings level slot:F)=rho (136+3*level.val+slot.val) :=
 representation.cast_value _
theorem leaf_meaning (representation : CanonicalRepresentation F) (rho : Nat → F) (c : TransferSem.Crypto) :
 MerkleInputMeaning28.registryMeaning rho=
 (TransferSem.assetLeaf (withHash c RegistryNatural193.small RegistryNatural193.wide representation)
   (recover representation rho):F) := RegistryNatural193.leaf_meaning rho _ (roles representation rho) c representation
end ShielddSecurity.RegistryRecovery194
'''
inputs={str(p):pin(p)for p in [W/'mac-registry-natural193-source01/source-root/ShielddSecurity/RegistryNatural193.lean',W/'mac-registry-epoch-semantic66-source03/source-root/ShielddSecurity/TransferSem.lean',W/'mac-initial734-completion19-source01/source-root/ShielddSecurity/CapturedInitial73419Generic01.lean']}
S.mkdir();(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes());(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
with(S/'templates01.json').open('x')as f:f.write(json.dumps(dict(modules={n:dict(body=b,names=['recover','roles','position_cast','position_canonical','siblings_cast','leaf_meaning'])},inputs=inputs,scope='SOURCE-only recovery of independent natural registry record from18 original field inputs plus position and48 siblings using canonical representatives. Original-column roles, position canonicality and leaf meaning derived, not supplied. Representation laws remain explicit; global path/point legality/full RegistrySem/native/full Transfer remain OPEN. All audits UNRUN.'),sort_keys=True,separators=(',',':'))+'\n')
