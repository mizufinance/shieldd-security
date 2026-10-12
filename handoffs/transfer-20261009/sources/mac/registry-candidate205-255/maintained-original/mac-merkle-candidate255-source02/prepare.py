from pathlib import Path
import sys,json,hashlib,runpy,re,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution277';S=W/'mac-merkle-candidate255-source02'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated');require(not S.exists(),'immutable');g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_ONLY');c=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);q=json.loads(Path(c['closure']['path']).read_bytes())['modules'];q.update(c['qualified_batch_imports']);modules={};inputs={}
for lev in range(15):
 old='CapturedMerkleGlobalLevel185L'+str(lev).zfill(2);v=q[old]['source'];require(pin(Path(v['path']))==v,'exact accepted level');inputs[v['path']]=v;raw=Path(v['path']).read_text();name='MerkleCandidateLevel255L'+str(lev).zfill(2)
 # Preserve exact accepted component names, including historical aliases/pilots.
 m=re.search(r'change AllSatisfied rho \[([^\]]+)\]',raw);require(m is not None,'exact flatten tuple');parts=[x.strip()[:-5]for x in m.group(1).split(',')]
 widths=[int(x)for x in re.search(r'def chunks.*?0 \[([0-9,]+)\]',raw).group(1).split(',')];require(len(parts)==len(widths) and sum(widths)==424 and all(x.endswith('rows')for x in m.group(1).split(',')),'exact accepted partition')
 facts=[]
 for ix,part in enumerate(parts):
  pv=q[part]['source'];require(pin(Path(pv['path']))==pv,'exact component');inputs[pv['path']]=pv;pr=Path(pv['path']).read_text();require('theorem checked' in pr or 'theorem globalChecked'in pr,'owned checker');check='globalChecked'if'theorem globalChecked'in pr else'checked'
  # Most pieces bind indices symbolically to local sparse rows; accepted source contracts fix range.
  start=3146+424*lev+sum(widths[:ix]);count=widths[ix]
  facts.append(f''' have b{ix} : Satisfies (CapturedFullRelation58.candidate base) {part}.rows := by
   apply CapturedArithmeticSelection252.candidate_rows base {part}.indices {part}.rows {part}.{check}
   change ∀ index∈List.range' {start} {count},CapturedArithmeticSelection252.Supported index
   exact CapturedArithmeticSelection252.range_supported {start} {count} (by omega)
''')
 tuple='True.intro'
 for ix in reversed(range(len(parts))):tuple='⟨b'+str(ix)+','+tuple+'⟩'
 body=f'''import ShielddSecurity.{old}
import ShielddSecurity.MerkleArithmeticConstruction253
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerAssertionBlock51 CompilerSelectedChunks172
open CapturedInitial73419Generic01 (p copy)
variable {{F : Type}} [Field F] [CharP F p]
theorem arithmetic (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleGlobalBody181.arithmeticRows {lev}) := by
'''+''.join(facts)+f''' rw [←{old}.partition]
 apply flatten_sound
 change AllSatisfied (CapturedFullRelation58.candidate base) [{','.join(x+'.rows'for x in parts)}]
 exact {tuple}
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) (MerkleFamily32Whole.rows (F:=F) {lev}) :=
 MerkleArithmeticConstruction253.body_rows base {lev} {old}.copy_checked (arithmetic base)
end ShielddSecurity.{name}
'''
 modules[name]=dict(body=body,names=['arithmetic','rows'])
for n in ['CapturedArithmeticSelection252','MerkleArithmeticConstruction253']:
 v=c['modules'][n]['source'];require(pin(Path(v['path']))==v,'future source pin');inputs[v['path']]=v
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+8*1024**2,'disk');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-merkle-sparse243-source02/generate.py').read_bytes());put('templates01.json',dict(modules=modules,inputs=inputs,scope=dict(status='SOURCE_ONLY_UNRUN',future_dependencies=['CapturedArithmeticSelection252','MerkleArithmeticConstruction253'],goal='Candidate selected rows for all fifteen later levels without full relation or target-row-truth premises',open=['All audits UNRUN','first level/prior/registry candidate transfer','legal assertion truth/native'],runtime=c['runtime_sha'],source_context=c['canonical_context'])))
print(json.dumps(dict(stage=str(S),modules=len(modules),reports=30,inputs=len(inputs))))
