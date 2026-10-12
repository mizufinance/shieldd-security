from pathlib import Path
import json,hashlib,sys,os,runpy
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-shared-subgroups269-source01';P=W/'mac-full-arithmetic45-execution296'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source');require(not S.exists(),'immutable');g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_ONLY');c=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);q=json.loads(Path(c['closure']['path']).read_bytes())['modules'];q.update(c['qualified_batch_imports']);inputs={}
for n in ['CapturedFourSubgroupSeed89','CapturedSubgroupSelection87']:
 v=q[n]['source'];require(pin(v['path'])==v,'qualified exact source');inputs[v['path']]=v
for root in [W/'mac-registry-seed-frame265-source03']:
 for v in json.loads((root/'generation01.json').read_bytes())['outputs']:inputs[v['source']['path']]=v['source']
 inputs[str(root/'generation01.json')]=pin(root/'generation01.json')
pre='set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\n';body='import ShielddSecurity.RegistrySeedFrame265\nimport ShielddSecurity.CapturedFourSubgroupSeed89\n'+pre+'''namespace ShielddSecurity.SharedSubgroups269
open Compiler CompilerArithmeticTransport41 PoseidonNatural192
theorem hint_checked : CapturedFourSubgroupSeed89.hintColumns.all (fun column => decide (column<49))=true := by decide +kernel
theorem hint_small (column : Nat) (member : column∈CapturedFourSubgroupSeed89.hintColumns) : column<49 :=
 of_decide_eq_true (List.all_eq_true.mp hint_checked column member)
theorem renamed_roles (group : Fin 4) (index : Nat) (bounds : 14≤index ∧ index≤20) :
 RegistrySeedFrame265.Protected (CapturedSubgroupSelection87.rename group index) := by
 rcases group with ⟨group,before⟩
 rcases bounds with ⟨lower,upper⟩
 interval_cases index <;> interval_cases group <;>
 norm_num [RegistrySeedFrame265.Protected,CapturedSubgroupSelection87.rename,CapturedFourSubgroups82.rename,CompilerWindowRenaming05.swap]
variable {F : Type} [Field F]
theorem completed_roles (base : Nat → F) (initial : Fin 4 → Group.Point F)
 (numbers : Nat → Nat) (fallback : Nat → Bool)
 (binding : ∀ group,CapturedFourSubgroupSeed89.Claimed base group=CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group)) :
 ∀ group,CapturedFourSubgroupConstructor88.InputRoles
 (fun column => SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback (CapturedSubgroupSelection87.rename group column)) (initial group) := by
 intro group
 have roles:=CapturedFourSubgroupSeed89.seeded_roles base initial group (binding group)
 have fixed (index : Nat) (bounds : 14≤index ∧ index≤20) :=
   RegistrySeedFrame265.completed_frame (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback
     (CapturedSubgroupSelection87.rename group index) (renamed_roles group index bounds)
 refine ⟨(fixed 14 (by omega)).trans roles.1,(fixed 15 (by omega)).trans roles.2.1,
   (fixed 16 (by omega)).trans roles.2.2.1,(fixed 17 (by omega)).trans roles.2.2.2.1,?_⟩
 intro index before
 exact (fixed (18+index) (by omega)).trans (roles.2.2.2.2 index before)
variable [CharP F p]
theorem all_four (base : Nat → F) (initial : Fin 4 → Group.Point F)
 (numbers : Nat → Nat) (fallback : Nat → Bool) (imaginary : F) (one : base 0=1)
 (binding : ∀ group,CapturedFourSubgroupSeed89.Claimed base group=CompilerSubgroupArithmetic79.eight (CapturedFirstSubgroup81.d:F) (initial group))
 (valid : ∀ group,Group.OnCurve (CapturedFirstSubgroup81.d:F) (initial group))
 (nonSquare : Group.NoUnitSquare (CapturedFirstSubgroup81.d:F)) (imaginarySquare : imaginary*imaginary = -1) :
 ∀ group,Satisfies (SharedWordWitness221.completed (CapturedFourSubgroupSeed89.seeded base initial) numbers fallback)
   (CapturedFourSubgroupConstructor88.originalRows group) := by
 let raw:=CapturedFourSubgroupSeed89.seeded base initial
 have originalZero : raw 0=base 0 := CapturedFourSubgroupSeed89.seeded_outside base initial 0 (by decide)
 have zero:=CapturedFullRelation58.candidate_outside (SharedWordWitness221.seeded raw numbers fallback) 0 (by omega) (by decide)
 have fixedZero:=SharedWordWitness221.seeded_fixed raw numbers fallback
 exact CapturedFourSubgroupConstructor88.all_four (SharedWordWitness221.completed raw numbers fallback) initial imaginary
   (zero.trans (fixedZero.1.trans (originalZero.trans one)))
   (CapturedFullRelation58.candidate_links (SharedWordWitness221.seeded raw numbers fallback)).2.2
   (SharedWordWitness221.arithmetic raw numbers fallback)
   (completed_roles base initial numbers fallback binding) valid nonSquare imaginarySquare
omit [CharP F p] in
theorem recover_frame (representation : CanonicalRepresentation F) (base : Nat → F)
 (initial : Fin 4 → Group.Point F) :
 RegistryRecovery194.recover representation (CapturedFourSubgroupSeed89.seeded base initial)=RegistryRecovery194.recover representation base := by
 unfold RegistryRecovery194.recover
 simp only ['''+','.join('CapturedFourSubgroupSeed89.seeded_outside base initial '+str(n)+' (by decide)'for n in [11,12,13,14,15,21,22,23,24,30,31,32,33,34,35,36,42,43,135])+''']
 congr 1
 funext level slot
 apply congrArg representation.value
 apply CapturedFourSubgroupSeed89.seeded_outside
 intro member
 have small:=hint_small (136+3*level.val+slot.val) member
 omega
omit [CharP F p] in
theorem anchor_frame (representation : CanonicalRepresentation F) (base : Nat → F)
 (initial : Fin 4 → Group.Point F) :
 representation.value (CapturedFourSubgroupSeed89.seeded base initial 4)=representation.value (base 4) :=
 congrArg representation.value (CapturedFourSubgroupSeed89.seeded_outside base initial 4 (by decide))
end ShielddSecurity.SharedSubgroups269
'''
names=['hint_checked','hint_small','renamed_roles','completed_roles','all_four','recover_frame','anchor_frame'];require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'source reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-original-anchor266-source02/generate.py').read_bytes());put('templates01.json',dict(modules=dict(SharedSubgroups269=dict(body=body,names=names)),inputs=inputs,scope=dict(status='SOURCE_ONLY_UNRUN',reports=7,goal='Four subgroup constructors on SAME shared Boolean/word/field-path candidate, using original-input role frame rather than unioning old candidate. Shared subgroup seed preserves original recovered registry/anchor.',premises=['Initial points on curve and exact eight-doubling binding; next legal semantic preimage wrapper will discharge','Base0=1, generic field/CharP p, nonsquare d/imaginary square certificates'],open=['Seven audits and frame dependency still UNRUN at preparation','Legal preimage ownership/concrete field model; shared word bounds/coherence/encoding','All assertions/native/full Transfer'],runtime=c['runtime_sha'],source_context=c['canonical_context'])))
