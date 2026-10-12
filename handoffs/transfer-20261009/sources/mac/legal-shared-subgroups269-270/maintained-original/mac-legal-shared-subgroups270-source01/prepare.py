from pathlib import Path
import json,hashlib,sys,os,runpy
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-legal-shared-subgroups270-source01';P=W/'mac-full-arithmetic45-execution297'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source');require(not S.exists(),'immutable');g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_ONLY');cfg=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);q=json.loads(Path(cfg['closure']['path']).read_bytes())['modules'];q.update(cfg['qualified_batch_imports']);inputs={}
for n in ['SubgroupSeedCompletion203','OriginalAnchor266']:
 v=q[n]['source'];require(pin(v['path'])==v,'accepted exact source');inputs[v['path']]=v
root=W/'mac-shared-subgroups269-source01'
for v in json.loads((root/'generation01.json').read_bytes())['outputs']:inputs[v['source']['path']]=v['source']
inputs[str(root/'generation01.json')]=pin(root/'generation01.json')
body='''import ShielddSecurity.SharedSubgroups269
import ShielddSecurity.SubgroupSeedCompletion203
import ShielddSecurity.OriginalAnchor266
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.LegalSharedSubgroups270
open Compiler CompilerArithmeticTransport41 PoseidonNatural192
variable {F J : Type} [Field F] [AddCommGroup J]
theorem field_encode (representation : CanonicalRepresentation F) (point : Group.Point F) :
 SubgroupSeedCompletion203.fieldPoint (RegistryPointSemantic200.encode representation point)=point := by
 cases point
 simp only [SubgroupSeedCompletion203.fieldPoint,RegistryPointSemantic200.encode,representation.cast_value]
theorem member_encoded (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 {d : F} (model : Group.StandardCurveModel J d) (point : Group.Point F)
 (valid : TransferSem.ValidPoint (RegistryPointSemantic200.interpret c representation model)
   (RegistryPointSemantic200.encode representation point)) : CapturedSubgroupModel199.Member model point := by
 have member:=SubgroupSeedCompletion203.member_of_valid c representation model _ valid
 rw [field_encode] at member
 exact member
theorem members_from_legal (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F)) (base : Nat → F)
 (w : TransferSem.Witness)
 (legal : TransferSem.RegistrySem (withHash (RegistryPointSemantic200.interpret c representation model)
   RegistryNatural193.small RegistryNatural193.wide representation) w)
 (registry : RegistryRecovery194.recover representation base=w.registry) :
 ∀ group,CapturedSubgroupModel199.Member model (CapturedFourSubgroupSeed89.Claimed base group) := by
 rcases legal with ⟨detection,ring,payload,checking,_,_,_,_,_,_,_⟩
 intro group
 apply member_encoded c representation model
 rcases group with ⟨group,before⟩
 interval_cases group
 · change TransferSem.ValidPoint (RegistryPointSemantic200.interpret c representation model) (RegistryRecovery194.recover representation base).detection
   rw [registry]
   exact detection
 · change TransferSem.ValidPoint (RegistryPointSemantic200.interpret c representation model) (RegistryRecovery194.recover representation base).ring
   rw [registry]
   exact ring
 · change TransferSem.ValidPoint (RegistryPointSemantic200.interpret c representation model) (RegistryRecovery194.recover representation base).audit.payload
   rw [registry]
   exact payload
 · change TransferSem.ValidPoint (RegistryPointSemantic200.interpret c representation model) (RegistryRecovery194.recover representation base).audit.checking
   rw [registry]
   exact checking
theorem legal_preimages (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F)) (base : Nat → F)
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1) (w : TransferSem.Witness)
 (legal : TransferSem.RegistrySem (withHash (RegistryPointSemantic200.interpret c representation model)
   RegistryNatural193.small RegistryNatural193.wide representation) w)
 (registry : RegistryRecovery194.recover representation base=w.registry) :
 ∃ initial : Fin 4 → Group.Point F,
 (∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group)) ∧
 ∀ group,CapturedFourSubgroupSeed89.Claimed base group=CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group) :=
 SubgroupSeedCompletion203.exists_initial model imaginary nonSquare imaginarySquare base
   (members_from_legal c representation model base w legal registry)
variable [CharP F p]
theorem shared_groups_and_anchor (c : TransferSem.Crypto) (representation : CanonicalRepresentation F)
 (model : Group.StandardCurveModel J (CapturedFirstSubgroup81.d:F)) (base : Nat → F)
 (imaginary : F) (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F))
 (imaginarySquare : imaginary*imaginary = -1) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (one : base 0=1)
 (coherent : SharedWordFlags220.Coherent (SharedWordFlags220.assignments SharedWordWitness221.wordSlots numbers))
 (position : numbers 135=representation.value (base 135)) (w : TransferSem.Witness)
 (legal : TransferSem.RegistrySem (withHash (RegistryPointSemantic200.interpret c representation model)
   RegistryNatural193.small RegistryNatural193.wide representation) w)
 (registry : RegistryRecovery194.recover representation base=w.registry)
 (anchor : representation.value (base 4)=w.assetAnchor) :
 ∃ initial : Fin 4 → Group.Point F,
 (∀ group,Satisfies (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback)
   (CapturedFourSubgroupConstructor88.originalRows group)) ∧
 ∃ row,CapturedFullRelation58.rowAt 178117=some row ∧
 Square (eval (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback) row.a)
   (eval (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback) row.b) := by
 obtain ⟨initial,valid,binding⟩:=legal_preimages c representation model base imaginary nonSquare imaginarySquare w legal registry
 refine ⟨initial,SharedSubgroups269.all_four base initial numbers fallback imaginary one binding valid nonSquare imaginarySquare,?_⟩
 have rawZero : CapturedFourSubgroupSeed89.seeded base initial 0=1 :=
   (CapturedFourSubgroupSeed89.seeded_outside base initial 0 (by decide)).trans one
 have rawPosition : numbers 135=representation.value (CapturedFourSubgroupSeed89.seeded base initial 135) :=
   position.trans (congrArg representation.value (CapturedFourSubgroupSeed89.seeded_outside base initial 135 (by decide))).symm
 exact OriginalAnchor266.anchor_from_original representation (RegistryPointSemantic200.interpret c representation model)
   (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback rawZero coherent rawPosition w legal
   ((SharedSubgroups269.recover_frame representation base initial).trans registry)
   ((SharedSubgroups269.anchor_frame representation base initial).trans anchor)
end ShielddSecurity.LegalSharedSubgroups270
'''
names=['field_encode','member_encoded','members_from_legal','legal_preimages','shared_groups_and_anchor'];require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'source reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-original-anchor266-source02/generate.py').read_bytes());put('templates01.json',dict(modules=dict(LegalSharedSubgroups270=dict(body=body,names=names)),inputs=inputs,scope=dict(status='SOURCE_ONLY_UNRUN',reports=5,goal='Independent legal interpreted RegistrySem yields original claimed point membership→owned four cofactor preimages→four actual subgroup families and178117 anchor on SAME shared word/Boolean/path candidate. No initial-validity/eight-binding/desired-hash/row-truth premise.',premises=['Concrete model/representation/nonsquare/imaginary certificates remain generic parameters here','Legal original registry/anchor encoding; base0=1; shared word coherence and canonical position selection'],open=['Five audits and269 still UNRUN at preparation','Owned native encoding/all66word bounds/seeded meanings/concreteCrypto','Remaining all assertions/native/full Transfer'],runtime=cfg['runtime_sha'],source_context=cfg['canonical_context'])))
