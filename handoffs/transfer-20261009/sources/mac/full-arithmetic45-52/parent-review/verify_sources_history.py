"""Review exact source census, generator successor and full retained attempt history."""
from pathlib import Path
import json,hashlib,re,shutil,subprocess,difflib
J=Path(__file__).parent;W=J.parent.parent;P=W/'mac-full-arithmetic45-kernel-result01';checked={}
def read(v):
 p=Path(v['path']);b=p.read_bytes();assert len(b)==v['bytes']and hashlib.sha256(b).hexdigest()==v['sha256'];checked[str(p)]=v;return b
mods={e['name']:e for e in json.loads((P/'qualified-modules01.json').read_bytes())}
aud=json.loads((J/'audit-result01.json').read_bytes());names={m['module']:[a['name']for a in m['audits']]for m in aud['modules']};public=[]
for n,e in mods.items():
 text=read(e['source']).decode();text=re.sub(r'/-.*?-/', '',text,flags=re.S);text=re.sub(r'--[^\n]*','',text);assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe|ofReduceBool|skipKernelTC)\b',text),n
 namespace=re.findall(r'^namespace ([\w.]+)\s*$',text,re.M);assert namespace==['ShielddSecurity.'+n]
 decls=[namespace[0]+'.'+m['name']for m in re.finditer(r'^(?P<mods>(?:(?:noncomputable|private|protected)\s+)*)(?:def|abbrev|theorem|lemma|structure|inductive|class)\s+(?P<name>[\w.]+)',text,re.M)if 'private'not in m['mods'].split()];assert decls==names[n];public+=decls
assert len(public)==len(set(public))==6012
scope=json.loads((P/'scope01.json').read_bytes())
for k in ['source_generation','data_qualification']:read(scope[k])
for v in scope['root_generation']:read(v)
for v in json.loads((P/'maintained-references01.json').read_bytes()):read(v)
pre=json.loads((J.parent/'full-arithmetic45-pre-review01/replay-review01.json').read_bytes());assert pre['qualification_sha256']==scope['data_qualification']['sha256']and pre['arithmetic_positions']==177954 and pre['leaves']==599
for e in pre['inventory']:assert e['source_sha256']==mods[e['module']]['source']['sha256']
S=W/'mac-full-arithmetic-root52-source02';T=W/'parent-full-arithmetic52-source-replay02';assert not T.exists();T.mkdir();shutil.copyfile(S/'generate.py',T/'generate.py');subprocess.run(['python3','-I','-B','-S',str(T/'generate.py')],check=True,capture_output=True,text=True,timeout=60)
outputs=json.loads((S/'generation01.json').read_bytes())['outputs']
for e in outputs:
 n=e['name'];assert(T/'source-root/ShielddSecurity'/(n+'.lean')).read_bytes()==read(mods[n]['source'])
old=(W/'mac-full-arithmetic-root52-source01/source-root/ShielddSecurity/CapturedFullArithmetic52.lean').read_text();new=(S/'source-root/ShielddSecurity/CapturedFullArithmetic52.lean').read_text()
expected=old.replace('(four_ne_zero (F:=F))','(CompilerArithmeticTransport41.four_ne_zero (F:=F))').replace('block rho (CompilerArithmeticTransport41.four_ne_zero (F:=F)) sat','block rho sat (CompilerArithmeticTransport41.four_ne_zero (F:=F))').replace('block base rho (CompilerArithmeticTransport41.four_ne_zero (F:=F)) agree sat','block base rho sat agree (CompilerArithmeticTransport41.four_ne_zero (F:=F))')
assert expected==new
history=json.loads((P/'attempt-history01.json').read_bytes());receipts=[json.loads(read(v))for v in history['receipts']];assert len(receipts)==history['all_attempts']==739;assert sum(r['status']=='passed'for r in receipts)==history['passed']==721
assert abs(sum(r['lean_seconds']for r in receipts)-history['all_lean_seconds'])<1e-8
failed=[]
for pin,r in zip(history['receipts'],receipts):
 if r['status']=='passed':continue
 assert r['status']=='failed'and r['cleanup']['clean']and r['error']is not None
 for k in ['source','stdout','stderr']:
  if r.get(k) is not None:read(r[k])
 failed.append(dict(receipt=pin,module=r['module'],source=r['source'],stdout=r['stdout'],stderr=r['stderr'],status='Rejected; no kernel acceptance or semantic negative result',exit=r['exit'],error=r['error'],cleanup_clean=True))
assert len(failed)==18 and [e['receipt']for e in failed]==[e['receipt']for e in history['failed']]
for e in mods.values():assert e['receipt']in history['receipts']
out=dict(kind='Independent public census/generation successor/preserved history review, no compiler',modules=610,declarations=6012,leaf_sources_matched_to_prior_independent_DATA_and_generator_replay=599,source_replay=11,repaired_root_delta='Fully qualify four_ne_zero and fix two argument orders; all contracts/group source bytes unchanged',original_receipts=739,passed_history=721,rejected_history=failed,rejected_attempts=18,all_rejected_cleanup_clean=True,pins_rehashed=len(checked),scope='Complete arithmetic partition only; assertion semantic truth, full Transfer and native refinement remain OPEN')
(J/'source-history-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='rejected_history'}))
