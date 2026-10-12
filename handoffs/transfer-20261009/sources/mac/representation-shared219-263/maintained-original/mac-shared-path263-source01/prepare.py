from pathlib import Path
import json,hashlib,sys,runpy,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution286';S=W/'mac-shared-path263-source01'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source');require(not S.exists(),'immutable');g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_ONLY');c=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);q=json.loads(Path(c['closure']['path']).read_bytes())['modules'];q.update(c['qualified_batch_imports']);inputs={}
for n in ['SharedWordWitness221','CapturedWordCompatibility251']:
 v=q[n]['source'];require(pin(v['path'])==v,'qualified primary source');inputs[v['path']]=v
root=W/'mac-candidate-path261-source01'
for x in json.loads((root/'generation01.json').read_bytes())['outputs']:
 if x['name']=='CandidateMerkleMeaning261':inputs[x['source']['path']]=x['source']
body='''import ShielddSecurity.SharedWordWitness221
import ShielddSecurity.CapturedWordCompatibility251
import ShielddSecurity.CandidateMerkleMeaning261
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedMerkleWitness263
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {F : Type} [Field F] [CharP F p]
theorem path (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (one : base 0=1) :
 eval (SharedWordWitness221.completed base numbers fallback) MerklePath33AnchorData.output=
 MerklePath33Meaning.meaning (CompilerVerifierLinks53.seeded (SharedWordWitness221.seeded base numbers fallback)) 15 :=
 CandidateMerkleMeaning261.output_seeded _ ((SharedWordWitness221.seeded_fixed base numbers fallback).1.trans one)
theorem shared (base : Nat → F) (numbers : Nat → Nat) (fallback : Nat → Bool)
 (one : base 0=1)
 (first : numbers 9059%2=numbers 9061%2)
 (second : numbers 10591%2=numbers 10593%2)
 (third : numbers 20935%2=numbers 20937%2)
 (bounded : ∀ entry∈CapturedWordRoot213.words,numbers entry.1.value<2^entry.1.width)
 (meanings : ∀ entry∈CapturedWordRoot213.words,SharedWordWitness221.seeded base numbers fallback entry.1.value=(numbers entry.1.value : F)) :
 CompilerArithmeticBlock44.SatisfiesAt (SharedWordWitness221.completed base numbers fallback) CapturedFullArithmetic52.rowAt 177954 ∧
 (∀ slot∈CapturedBooleanRoot209.slots,∃ row,CapturedFullRelation58.rowAt (177954+slot.1)=some row ∧
 Square (eval (SharedWordWitness221.completed base numbers fallback) row.a) (eval (SharedWordWitness221.completed base numbers fallback) row.b)) ∧
 (∀ entry∈CapturedWordRoot213.words,∃ row,CapturedFullRelation58.rowAt (177954+entry.1.position)=some row ∧
 Square (eval (SharedWordWitness221.completed base numbers fallback) row.a) (eval (SharedWordWitness221.completed base numbers fallback) row.b)) ∧
 eval (SharedWordWitness221.completed base numbers fallback) MerklePath33AnchorData.output=
 MerklePath33Meaning.meaning (CompilerVerifierLinks53.seeded (SharedWordWitness221.seeded base numbers fallback)) 15 :=
 ⟨SharedWordWitness221.arithmetic base numbers fallback,
  SharedWordWitness221.boolean_rows base numbers fallback,
  SharedWordWitness221.word_rows base numbers fallback
    (CapturedWordCompatibility251.coherent numbers first second third) bounded meanings,
  path base numbers fallback one⟩
end ShielddSecurity.SharedMerkleWitness263
'''
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'small source floor');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-merkle-sparse243-source02/generate.py').read_bytes());put('templates01.json',dict(modules=dict(SharedMerkleWitness263=dict(body=body,names=['path','shared'])),inputs=inputs,scope=dict(status='SOURCE_ONLY_UNRUN',reports=2,future=['CandidateMerkleMeaning261'],goal='ONE same-assignment unconditional arithmetic+Boolean+conditional word reconstruction AND independent16-level field path. Does not combine with historical1467-assertion candidate.',premises=['Base0=1','Exactly three word parity equalities','66 bounded natural numbers and explicitly seeded cast meanings'],open=['Legal-source derivations of those premises/seed compatibility','Actual anchor assertion/concrete natural crypto and remaining all assertion truth','Native/state/Host/durability/full Transfer'],runtime=c['runtime_sha'],source_context=c['canonical_context'])))
print(json.dumps(dict(stage=str(S),reports=2)))
