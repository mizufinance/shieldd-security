"""Read-only census, exact small source regeneration and preserved join history."""
from pathlib import Path
import hashlib,json,re,subprocess,shutil,difflib
W=Path(__file__).parent.parent;J=Path(__file__).parent
tasks=[('full-captured-epoch64','mac-full-captured-epoch64-kernel-result01'),('registry-epoch66','mac-registry-epoch-semantic66-kernel-result01'),('global-zero68','mac-global-zero-completion68-kernel-result01')]
replayed={};checked={}
def read(r):
 p=Path(r['path']);b=p.read_bytes();assert len(b)==r['bytes']and hashlib.sha256(b).hexdigest()==r['sha256'];checked[str(p)]=r;return b
for label,packet in tasks:
 D=J/(label+'-review01');P=W/packet;mods=json.loads((P/'qualified-modules01.json').read_bytes());audit=json.loads((D/'audit-result01.json').read_bytes());names={e['module']:[a['name']for a in e['audits']]for e in audit['modules']}
 for e in mods:
  n=e['name'];text=read(e['source']).decode();clean=re.sub(r'/-.*?-/', '',text,flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
  public=['ShielddSecurity.'+n+'.'+m['name']for m in re.finditer(r'^(?P<mods>(?:(?:noncomputable|private|protected|local)\s+)*)(?:def|abbrev|theorem|lemma|structure|inductive|class|instance)\s+(?P<name>[\w.]+)',clean,re.M)if 'private'not in m['mods'].split()]
  unaudited=[v for v in public if v not in names[n]]
  assert unaudited==(['ShielddSecurity.TransferSem.Path']if n=='TransferSem'else[]),n
  assert [v for v in public if v not in unaudited]==names[n],n
  assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe|ofReduceBool|skipKernelTC)\b',clean)
  S=Path(e['source']['path']).parents[2]
  if S not in replayed:
   T=D/'source-replay03'/S.name;T.mkdir(parents=True)
   for f in ['generate.py','template.lean','input-pins01.json','dependencies01.json']:
    if(S/f).is_file():shutil.copyfile(S/f,T/f)
   r=subprocess.run(['python3','-I','-B','-S',str(T/'generate.py')],capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stderr
   replayed[S]=T
  assert(replayed[S]/'source-root/ShielddSecurity'/(n+'.lean')).read_bytes()==read(e['source']),n
 for r in json.loads((P/'maintained-references01.json').read_bytes()):read(r)
 history=json.loads((P/'attempt-history01.json').read_bytes());receipts=[json.loads(read(r))for r in history['receipts']];assert len(receipts)==history['all_attempts']and sum(r['status']=='passed'for r in receipts)==history['passed'];assert abs(sum(r['lean_seconds']for r in receipts)-history['all_lean_seconds'])<1e-8
 rejected=[]
 for pin,r in zip(history['receipts'],receipts):
  if r['status']=='passed':continue
  assert r['status']=='failed'and r['cleanup']['clean']and r['error']is not None
  for key in ['source','stdout','stderr']:
   if r.get(key)is not None:read(r[key])
  rejected.append(dict(receipt=pin,module=r['module'],source=r['source'],stdout=r['stdout'],stderr=r['stderr'],exit=r['exit'],error=r['error'],cleanup_clean=True,scope='Rejected predecessor; no semantic negative result'))
 assert [r['receipt']for r in rejected]==[r['receipt']for r in history['failed']]
 for e in mods:assert e['receipt']in history['receipts']
 out=dict(kind='Explicit source census, isolated maintained source byte replay and complete original history; no Lean execution',modules=len(mods),reports=audit['declarations'],unaudited_transparent_abbreviations=['ShielddSecurity.TransferSem.Path']if label=='registry-epoch66'else[],replayed_sources=len(mods),history_attempts=len(receipts),history_passed=history['passed'],rejected=rejected,pins_rehashed=len(checked),full_transfer='OPEN')
 (D/'source-history-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k!='rejected'}))
