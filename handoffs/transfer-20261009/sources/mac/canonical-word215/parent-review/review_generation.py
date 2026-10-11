from pathlib import Path
import json,re,hashlib,subprocess,shutil
J=Path(__file__).parent;W=J.parent.parent;P=W/'mac-canonical-word215-kernel-result01';T=J/'source-replay01';T.mkdir()
def pin(p):return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
mods=json.loads((P/'source-object-receipt01.json').read_text());aud=json.loads((J/'audit-result01.json').read_text());names={e['module']:[a['name']for a in e['audits']]for e in aud['modules']}
roots={};checked=[]
for e in mods:
 p=Path(e['source']['path']);s=p.read_text();assert pin(p)==e['source'];clean=re.sub(r'/-.*?-/', '',s,flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 ns=re.findall(r'^namespace ([\w.]+)',clean,re.M);assert len(ns)==1
 exports=[ns[0]+'.'+m['name']for m in re.finditer(r'^[ \t]*(?P<mods>(?:(?:noncomputable|private|protected|local)\s+)*)(?:def|abbrev|theorem|lemma|structure|inductive|class|instance)\s+(?P<name>[\w.]+)',clean,re.M)if not({'private','local'}&set(m['mods'].split()))]
 assert len(exports)==len(set(exports)) and set(exports)==set(names[e['module']]),e['module']
 assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe|ofReduceBool|skipKernelTC)\b',clean)
 roots.setdefault(p.parents[2],[]).append(e)
for s,entries in roots.items():
 producer=json.loads((s/'producer-manifest01.json').read_text())
 for z in producer.values():assert pin(Path(z['path']))==z;checked.append(z)
 r=T/s.name;r.mkdir()
 for p in [s/'generate.py',s/'templates01.json']:shutil.copyfile(p,r/p.name)
 result=subprocess.run(['python3','-I','-B','-S',str(r/'generate.py')],capture_output=True,text=True,timeout=60);assert result.returncode==0,result.stderr
 for e in entries:assert(r/'source-root/ShielddSecurity'/(e['module']+'.lean')).read_bytes()==Path(e['source']['path']).read_bytes()
report=dict(status='PASSED',kind='Exact isolated maintained template generation and complete public declaration census, no Lean execution',modules=len(mods),reports=aud['declarations'],roots=[str(r)for r in roots],original_pins_checked=len(checked),all_public_names_audited=True,regenerated_source_exact=True,scope='Generic symbolic canonical word recovery from decoded Boolean assignment, checked comparison/reconstruction and independently supplied max p-1/final acceptance. Concrete14 terminal/max bindings, global legal seed/all assertions/native/full Transfer OPEN',full_transfer='OPEN')
(J/'source-generation-review01.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
