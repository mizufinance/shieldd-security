from pathlib import Path
import json,hashlib,sys,runpy,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution285';S=W/'mac-candidate-path261-source01'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source preparation');require(not S.exists(),'immutable source successor');g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_ONLY');c=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);q=json.loads(Path(c['closure']['path']).read_bytes())['modules'];q.update(c['qualified_batch_imports']);inputs={};future=[];modules={}
for root in [W/'mac-candidate-collectors259-source02']:
 for v in json.loads((root/'generation01.json').read_bytes())['outputs']:
  require(pin(v['source']['path'])==v['source'],'frozen future source');inputs[v['source']['path']]=v['source'];future.append(v['name'])
pre='set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\n'
head='open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41\nvariable {F : Type} [Field F] [CharP F p]\n'
def body(name,imports,text,names):
 for n in imports:
  if n in q:v=q[n]['source'];require(pin(v['path'])==v,'qualified exact source');inputs[v['path']]=v
  else:require(n in future or n in modules,'closed named future import')
 modules[name]=dict(body=''.join('import ShielddSecurity.'+n+'\n'for n in imports)+pre+'namespace ShielddSecurity.'+name+'\n'+head+text+'end ShielddSecurity.'+name+'\n',names=names)
body('CandidateMerkleSelection261',['CapturedMerkleFirstSelection186','CapturedArithmeticSelection252'],'''theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) MerkleSelection26Data.originalRows := by
 apply CapturedArithmeticSelection252.candidate_rows base CapturedMerkleFirstSelection186.indices _ CapturedMerkleFirstSelection186.checked
 intro index member
 change index∈List.range' 2722 12++[200769] at member
 rcases List.mem_append.mp member with arithmetic|copying
 · exact CapturedArithmeticSelection252.range_supported 2722 12 (by omega) index arithmetic
 · right
   exact List.mem_singleton.mp copying
''',['rows'])
body('CandidateMerklePrior261',['CandidatePriorRows259','CandidateThreeCallRows259','CandidateRegistryRows259','CandidateMerkleSelection261','MerkleHash27Whole'],'''theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) MerkleHash27Whole.priorRows := by
 intro row member
 simp only [MerkleHash27Whole.priorRows,List.mem_append] at member
 rcases member with ((before|joined)|registry)|selected
 · exact CandidatePriorRows259.rows base row before
 · exact CandidateThreeCallRows259.rows base row joined
 · exact CandidateRegistryRows259.rows base row registry
 · exact CandidateMerkleSelection261.rows base row selected
''',['rows'])
levels=['MerkleCandidateLevel255L'+str(i).zfill(2)for i in range(15)]
cases='|'.join('rfl'for _ in levels)
text='''theorem level_rows (base : Nat → F) (i : Fin 15) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) i) := by
 have cases : '''+' ∨ '.join('i='+str(i)for i in range(15))+''' := by
   have bound:=i.isLt
   simp only [Fin.ext_iff]
   omega
 rcases cases with '''+cases+'\n'+''.join(' · exact '+n+'.rows base\n'for n in levels)+'''theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerklePath33.rows (F:=F)) := by
 change Satisfies (CapturedFullRelation58.candidate base) (CompilerSegmentChain33.rows copy (MerklePath33.piece (F:=F)) 15)
 apply CompilerIndexedSlices183.chain_sound
 intro i less
 change Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) ⟨i%15,Nat.mod_lt i (by decide)⟩)
 exact level_rows base _
'''
body('CandidateMerkleRest261',[*levels,'MerklePath33Meaning','CompilerIndexedSlices183'],text,['level_rows','rows'])
body('CandidateMerkleMeaning261',['CandidateMerklePrior261','CandidateFirstMerkleRows259','CandidateMerkleRest261','MerkleArithmeticConstruction253'],'''theorem output (base : Nat → F) (one : base 0=1) :
 eval (CapturedFullRelation58.candidate base) MerklePath33AnchorData.output=
 MerklePath33Meaning.meaning (CapturedFullRelation58.candidate base) 15 :=
 MerklePath33Meaning.arbitrary _ (MerkleArithmeticConstruction253.candidate_zero base one)
   (CandidateMerklePrior261.rows base) (CandidateFirstMerkleRows259.rows base) (CandidateMerkleRest261.rows base)
omit [CharP F p] in
theorem input_frame (base : Nat → F) (column : Nat) (below : column<22738) :
 CapturedFullRelation58.candidate base column=CompilerVerifierLinks53.seeded base column :=
 CapturedFullArithmetic52.outside _ column (Or.inl below)
omit [CharP F p] in
theorem meaning_seeded (base : Nat → F) :
 MerklePath33Meaning.meaning (CapturedFullRelation58.candidate base) 15=
 MerklePath33Meaning.meaning (CompilerVerifierLinks53.seeded base) 15 :=
 MerklePath33Meaning.meaning_agrees _ _ (input_frame base) 15
theorem output_seeded (base : Nat → F) (one : base 0=1) :
 eval (CapturedFullRelation58.candidate base) MerklePath33AnchorData.output=
 MerklePath33Meaning.meaning (CompilerVerifierLinks53.seeded base) 15 :=
 (output base one).trans (meaning_seeded base)
''',['output','input_frame','meaning_seeded','output_seeded'])
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'small source reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-merkle-sparse243-source02/generate.py').read_bytes());put('templates01.json',dict(modules=modules,inputs=inputs,scope=dict(status='SOURCE_ONLY_UNRUN',modules=4,reports=8,future_dependencies=future,goal='Independent full sixteen-level candidate field path from unconditional all-arithmetic/copy constructor; no FullSAT, selected-row truth, or desired hash premise',open=['All eight audits UNRUN','Legal root equality/anchor assertion, Boolean legal seed, remaining all-assertion truth, concrete natural representation, native/full Transfer'],runtime=c['runtime_sha'],source_context=c['canonical_context'])))
print(json.dumps(dict(stage=str(S),modules=4,reports=8)))
