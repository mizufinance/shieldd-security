from pathlib import Path
import json,hashlib,sys,runpy,re,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-arithmetic45-execution281';S=W/'mac-prefix-candidate258-source02'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated');require(not S.exists(),'immutable');g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_ONLY');c=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);q=json.loads(Path(c['closure']['path']).read_bytes())['modules'];q.update(c['qualified_batch_imports']);inputs={};modules={};mapping=[];groups={}
def indices(name,depth=0):
 require(depth<5,'bounded source alias depth');v=q[name]['source'];require(pin(Path(v['path']))==v,'exact index-source');inputs[v['path']]=v;raw=Path(v['path']).read_text();m=re.search(r'def indices\s*:\s*List Nat\s*:=\s*List\.range\x27\s+(\d+)\s+(\d+)',raw)
 if m:return tuple(map(int,m.groups()))
 m=re.search(r'def indices\s*:\s*List Nat\s*:=\s*(\w+)\.indices',raw);require(m is not None,'literal/qualified-alias indices '+name);return indices(m.group(1),depth+1)
parents=['CapturedCall04GlobalBinding168','CapturedPriorGlobalBinding170','CapturedThreeCallGlobalBinding173','CapturedRegistryGlobalBinding175','CapturedMerkleFirstGlobal186']
for parent in parents:
 v=q[parent]['source'];require(pin(Path(v['path']))==v,'exact accepted collector');inputs[v['path']]=v;raw=Path(v['path']).read_text();m=re.search(r'change AllSatisfied rho \[([^\]]+)\]',raw)
 if m:parts=[x.strip()[:-5]for x in m.group(1).split(',')]
 else:
  require(parent=='CapturedCall04GlobalBinding168','known concatenation collector');signature=raw.split('theorem partition :',1)[1].split(':= by',1)[0];parts=re.findall(r'(\w+)\.rows',signature)
 require(len(parts)==len(set(parts)),'exact no duplicate parts');groups[parent]=parts
 for original in parts:
  if any(x['original']==original for x in mapping):continue
  v=q[original]['source'];require(pin(Path(v['path']))==v,'exact accepted part');inputs[v['path']]=v;r=Path(v['path']).read_text();start,count=indices(original);require(count>0 and start+count<=177954,'arithmetic support');ch=re.search(r'productionCheck.*?CompilerIndexedCopy(\w+)\.check',r,re.S);require(ch is not None,'exact checker family');kind=ch.group(1);require(kind in ['Constant178','Stream171','Collection174','Selection166'],'supported family '+original+' '+kind);helper={'Constant178':'CapturedPackedCandidate257.rows','Stream171':'CapturedArithmeticSelection252.candidate_rows','Collection174':'CapturedCollectionCandidate256.rows','Selection166':'CapturedIndexedCandidate260.rows'}[kind];dep=helper.split('.')[0];name='CandidateRows258P'+str(len(mapping)).zfill(3);checked='globalChecked'if'theorem globalChecked'in r else'checked';require('theorem '+checked in r,'owned finite checker')
  body=f'''import ShielddSecurity.{original}
import ShielddSecurity.{dep}
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.{name}
open Compiler CompilerAssertionBlock51 CompilerArithmeticTransport41
variable {{F : Type}} [Field F] [CharP F p]
theorem rows (base : Nat → F) : Satisfies (CapturedFullRelation58.candidate base) {original}.rows := by
 apply {helper} base {original}.indices {original}.rows {original}.{checked}
 change ∀ index∈List.range' {start} {count},CapturedArithmeticSelection252.Supported index
 exact CapturedArithmeticSelection252.range_supported {start} {count} (by omega)
end ShielddSecurity.{name}
'''
  modules[name]=dict(body=body,names=['rows']);mapping.append(dict(module=name,original=original,source=v,parent=parent,start=start,count=count,checker=kind,checked=checked))
for dep in ['CapturedArithmeticSelection252','CapturedCollectionCandidate256','CapturedPackedCandidate257','CapturedIndexedCandidate260']:
 v=q[dep]['source']if dep in q else c['modules'][dep]['source'];require(pin(Path(v['path']))==v,'exact helper source');inputs[v['path']]=v
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+8*1024**2,'safe source reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-merkle-sparse243-source02/generate.py').read_bytes());put('position-map01.json',dict(parts=mapping,collectors=groups,scope='Exact accepted collector ordered component names and literal arithmetic range metadata; every checker remains an existing qualified theorem, no new row/source qualification by DATA alone'));put('templates01.json',dict(modules=modules,inputs=inputs,scope=dict(status='SOURCE_ONLY_UNRUN',planned_modules=len(modules),planned_reports=len(mapping),goal='Independent Full58.candidate selected arithmetic row constructors for Call04/prior/Join/registry/first-Merkle pieces, without FullSAT or selected-row/hash truth assumptions',future_dependencies=['CapturedIndexedCandidate260'],open=['All new audits UNRUN','Symbolic collectors/copy assembly','Total legal seed/all assertions/native/full Transfer'],runtime=c['runtime_sha'],source_context=c['canonical_context'])))
print(json.dumps(dict(stage=str(S),modules=len(modules),sources=len(inputs),positions=sum(x['count']for x in mapping))))
