from pathlib import Path
import sys,json,hashlib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-registry-natural193-source01'
def require(v,m):
 if not v:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site and not sys.flags.optimize,'isolated')
require(not S.exists(),'fresh immutable source')
n='RegistryNatural193'
roles=[('value',11,'l.value'),('nextIndex',12,'l.nextIndex'),('nextValue',13,'l.nextValue'),('detectionX',14,'l.detection.x'),('detectionY',15,'l.detection.y'),('dailyLimit',21,'l.dailyLimit'),('routePolicy',22,'l.routePolicy'),('ringX',23,'l.ring.x'),('ringY',24,'l.ring.y'),('ringID',30,'l.ringID'),('policyID',31,'l.policyID'),('permission',32,'l.permission'),('resource',33,'l.resource'),('epoch',34,'l.audit.epoch'),('payloadX',35,'l.audit.payload.x'),('payloadY',36,'l.audit.payload.y'),('checkingX',42,'l.audit.checking.x'),('checkingY',43,'l.audit.checking.y')]
b='''import ShielddSecurity.PoseidonNatural192
import ShielddSecurity.MerkleInputMeaning28
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegistryNatural193
variable {F : Type} [Field F]
open PoseidonNatural192
def fieldLeaf (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
 (l : TransferSem.AssetLeaf) : F :=
 Poseidon.hash6 wide 25 [(l.value:F),(l.nextIndex:F),(l.nextValue:F),
   Poseidon.hash6 wide 23 [(l.detection.x:F),(l.detection.y:F),(l.dailyLimit:F),(l.routePolicy:F)],
   Poseidon.hash3 small 24 [
     Poseidon.hash6 wide 24 [(l.ring.x:F),(l.ring.y:F),(l.ringID:F),(l.policyID:F),(l.permission:F),(l.resource:F)],
     Poseidon.hash6 wide 36 [(l.audit.epoch:F),(l.audit.payload.x:F),(l.audit.payload.y:F),(l.audit.checking.x:F),(l.audit.checking.y:F)]]]
theorem assetLeaf_cast (c : TransferSem.Crypto) (small : Poseidon.Parameters F 3)
 (wide : Poseidon.Parameters F 6) (representation : CanonicalRepresentation F) (l : TransferSem.AssetLeaf) :
 (TransferSem.assetLeaf (withHash c small wide representation) l:F)=fieldLeaf small wide l := by
 simp [TransferSem.assetLeaf,TransferSem.pointFields,withHash_cast,Poseidon.hash,TransferSem.domainCode,fieldLeaf]
structure Roles (rho : Nat → F) (l : TransferSem.AssetLeaf) : Prop where
'''+''.join(' '+name+' : rho '+str(column)+'=('+term+':F)\n'for name,column,term in roles)+'''
def small : Poseidon.Parameters F 3 := Poseidon.castParameters TransferPoseidonWidth3Call08Shared01.parameters
def wide : Poseidon.Parameters F 6 := Poseidon.castParameters TransferPoseidonCall04Shared01.parameters
theorem field_roles (rho : Nat → F) (l : TransferSem.AssetLeaf) (roles : Roles rho l) :
 MerkleInputMeaning28.registryMeaning rho=fieldLeaf small wide l := by
 simp only [MerkleInputMeaning28.registryMeaning,RegistryInputJoin24.semanticInputs,fieldLeaf,small,wide,
 '''+','.join('roles.'+name for name,_,_ in roles)+''']
theorem leaf_meaning (rho : Nat → F) (l : TransferSem.AssetLeaf) (roles : Roles rho l)
 (c : TransferSem.Crypto) (representation : CanonicalRepresentation F) :
 MerkleInputMeaning28.registryMeaning rho=
 (TransferSem.assetLeaf (withHash c small wide representation) l:F) := by
 rw [assetLeaf_cast]
 exact field_roles rho l roles
end ShielddSecurity.RegistryNatural193
'''
inputs={str(p):pin(p)for p in [W/'mac-poseidon-natural192-source01/source-root/ShielddSecurity/PoseidonNatural192.lean',W/'mac-merkle-input-meaning28-batch01/source-root/ShielddSecurity/MerkleInputMeaning28.lean',W/'mac-registry-input-join24-continuation02/source-root/ShielddSecurity/RegistryInputJoin24.lean',W/'mac-registry-epoch-semantic66-source03/source-root/ShielddSecurity/TransferSem.lean']}
S.mkdir();(S/'generate.py').write_bytes((W/'mac-indexed-slices183-source01/generate.py').read_bytes());(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
with(S/'templates01.json').open('x')as f:f.write(json.dumps(dict(modules={n:dict(body=b,names=['fieldLeaf','assetLeaf_cast','Roles','small','wide','field_roles','leaf_meaning'])},inputs=inputs,scope='SOURCE-only natural semantic registry leaf cast under independently defined canonical Poseidon interpretation and18 explicit original-column field-role bindings. Exact arities4/6/5/2/5; no desired hash/row satisfaction premise. Actual canonical representation, full path/root/RegistrySem/native/full Transfer remain OPEN. All audits UNRUN.'),sort_keys=True,separators=(',',':'))+'\n')
