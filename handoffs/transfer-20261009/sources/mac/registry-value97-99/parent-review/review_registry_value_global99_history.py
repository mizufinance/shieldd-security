"""Exact maintained source regeneration and original endpoint histories."""
from pathlib import Path
import hashlib,json,re,subprocess,shutil
J=Path(__file__).parent;W=J.parent;Q=W/'mac-registered-audit70-data01/qualification01.json'
tasks=[('registry-value-global98-99','mac-registry-value-global98-99-kernel-result01')]
checked={}
def read(pin):
 p=Path(pin['path']);b=p.read_bytes();assert len(b)==pin['bytes']and hashlib.sha256(b).hexdigest()==pin['sha256'],p;checked[str(p)]=pin;return b
for label,packet in tasks:
 D=J/(label+'-review01');P=W/packet;T=D/'source-replay01';T.mkdir()
 mods=json.loads((P/'qualified-modules01.json').read_bytes());audit=json.loads((D/'audit-result01.json').read_bytes());names={e['module']:[a['name']for a in e['audits']]for e in audit['modules']}
 for e in mods:
  n=e['name'];source=read(e['source']).decode();clean=re.sub(r'/-.*?-/', '',source,flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
  prefix=re.findall(r'^namespace ([\w.]+)',clean,re.M);assert len(prefix)==1
  public=[prefix[0]+'.'+m['name']for m in re.finditer(r'^(?P<mods>(?:(?:noncomputable|private|protected|local)\s+)*)(?:def|abbrev|theorem|lemma|structure|inductive|class|instance)\s+(?P<name>[\w.]+)',clean,re.M)if not({'private','local'}&set(m['mods'].split()))]
  assert public==names[n],n
  assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe|ofReduceBool|skipKernelTC)\b',clean)
  S=Path(e['source']['path']).parents[2];R=T/S.name;R.mkdir()
  for file in ['generate.py','template.lean','input-pins01.json','dependencies01.json','selected-data01.json','data-template.lean','proof-template.lean']:
   if(S/file).is_file():shutil.copyfile(S/file,R/file)
  run=subprocess.run(['python3','-I','-B','-S',str(R/'generate.py')],capture_output=True,text=True,timeout=60);assert run.returncode==0,run.stderr
  assert(R/'source-root/ShielddSecurity'/(n+'.lean')).read_bytes()==read(e['source']),n
 for pin in json.loads((P/'maintained-references01.json').read_bytes()):read(pin)
 h=json.loads((P/'attempt-history01.json').read_bytes());receipts=[json.loads(read(pin))for pin in h['receipts']]
 assert len(receipts)==h['all_attempts']and sum(r['status']=='passed'for r in receipts)==h['passed']
 assert abs(sum(r['lean_seconds']for r in receipts)-h['all_lean_seconds'])<1e-8
 rejected=[]
 for pin,r in zip(h['receipts'],receipts):
  if r['status']=='passed':continue
  assert r['status']=='failed'and r['cleanup']['clean']and r['error']is not None
  for key in ['source','stdout','stderr']:
   if r.get(key)is not None:read(r[key])
  rejected.append(dict(receipt=pin,module=r['module'],source=r['source'],stdout=r['stdout'],stderr=r['stderr'],exit=r['exit'],error=r['error'],cleanup_clean=True,scope='Rejected original attempt; no semantic negative result'))
 assert [r['receipt']for r in rejected]==[r['receipt']for r in h['failed']]
 assert all(e['receipt']in h['receipts']for e in mods)
 out=dict(kind='Independent public source census, exact isolated maintained generation and complete original receipt history; no Lean execution',modules=len(mods),reports=audit['declarations'],all_exported_declarations_audited=True,source_replay_exact=True,history_attempts=len(receipts),history_passed=h['passed'],rejected=rejected,pins_rehashed=len(checked),scope=json.loads((P/'scope01.json').read_bytes()),full_transfer='OPEN')
 (D/'source-history-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:v for k,v in out.items()if k not in ['rejected','scope']}))
