"""Review producer source references, public census, generators and failed history."""
from pathlib import Path
import hashlib,json,re,shutil,subprocess,difflib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');J=W/'resumed-orchestration-20261009-01/assertion-provider50-review01';P=W/'mac-assertion-provider50-kernel-result01';PRE=J.parent/'assertion-provider50-pre-review01'
checked={}
def read(v):
 p=Path(v['path']);assert p.is_file()and not p.is_symlink(),p;b=p.read_bytes();assert len(b)==v['bytes']and hashlib.sha256(b).hexdigest()==v['sha256'],p;checked[str(p)]=v;return b
refs=json.loads((P/'references01.json').read_bytes())
for key,v in refs.items():
 if isinstance(v,dict)and {'path','bytes','sha256'}<=set(v):read(v)
mods=json.loads((P/'qualified-modules01.json').read_bytes());aud=json.loads((J/'audit-result01.json').read_bytes());audits={m['module']:[a['name']for a in m['audits']]for m in aud['modules']};public=[]
for name,v in mods.items():
 text=read(v['source']).decode();stripped=re.sub(r'/-.*?-/', '', text, flags=re.S);stripped=re.sub(r'--[^\n]*','',stripped)
 assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|axiom|unsafe|ofReduceBool|skipKernelTC)\b',stripped),name
 namespaces=re.findall(r'^namespace ([\w.]+)\s*$',stripped,re.M);assert namespaces==['ShielddSecurity.'+name],(name,namespaces)
 declarations=[]
 for m in re.finditer(r'^(?P<mods>(?:(?:noncomputable|private|protected)\s+)*)(?:def|abbrev|theorem|lemma|structure|inductive|class)\s+(?P<name>[\w.]+)',stripped,re.M):
  if 'private'not in m['mods'].split():declarations.append(namespaces[0]+'.'+m['name'])
 assert declarations==audits[name],name;public+=declarations
assert len(public)==842
expected=json.loads((W/'mac-assertion-provider50-portable-source01/expected-sources01.json').read_bytes())
for name,v in expected.items():assert {k:mods[name]['source'][k]for k in ['bytes','sha256']}=={k:v[k]for k in ['bytes','sha256']}
for name in ['CapturedFullAssertions54',*[f'CapturedAssertions54G{i:02d}'for i in range(6)]]:
 v=mods[name]['source'];assert read(v)==(PRE/'root54-regeneration01/source-root/ShielddSecurity'/(name+'.lean')).read_bytes()
reg=[]
for folder,module in [('mac-assertion-controls56-source01','CapturedAssertionControls56'),('mac-assertion-links57-source02','CapturedAssertionLinks57')]:
 S=W/folder;R=J/'regenerated'/folder
 if not R.exists():
  R.mkdir(parents=True)
  for n in ['generate.py','template.lean']:shutil.copyfile(S/n,R/n)
  r=subprocess.run(['python3','-I','-B','-S',str(R/'generate.py')],capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stderr
 for n in ['generate.py','template.lean']:assert (S/n).read_bytes()==(R/n).read_bytes()
 actual=R/'source-root/ShielddSecurity'/(module+'.lean');assert actual.read_bytes()==read(mods[module]['source']);reg.append({'module':module,'source':mods[module]['source'],'unchanged_generator_sha256':hashlib.sha256((R/'generate.py').read_bytes()).hexdigest()})
a=(W/'mac-assertion-links57-source01/template.lean').read_bytes();b=(W/'mac-assertion-links57-source02/template.lean').read_bytes();needle=b'theorem copy_of_truth';assert a.replace(needle,b'omit [CharP F p] in\n'+needle)==b
history=json.loads(read(refs['carried_history']));allpins=history['receipts']+[{'path':str(p),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}for p in sorted((W/'mac-assertion-provider50-execution10/runtime/receipts').glob('*.json'))]
allreceipts=[json.loads(read(v))for v in allpins];assert len(allreceipts)==400
fail=json.loads((P/'failed-attempts01.json').read_bytes());failed=[]
for v in fail:
 r=json.loads(read(v['receipt']));assert r['status']=='failed'and r['error']is not None and r['cleanup']['clean']
 assert r['source']==v['source']and r['stdout']==v['stdout']and r['stderr']==v['stderr']
 for k in ['source','stdout','stderr']:read(v[k])
 failed.append({'module':r['module'],'receipt':v['receipt'],'source':v['source'],'status':'failed; zero kernel acceptance','exit':r['exit'],'error':r['error'],'cleanup_clean':True})
assert sum(r['status']=='failed'for r in allreceipts)==len(failed)==13
assert [v['receipt']for v in fail]==[v for v,r in zip(allpins,allreceipts)if r['status']=='failed']
for n,v in mods.items():assert v['receipt']in allpins,n
scope=json.loads((P/'scope01.json').read_bytes());assert abs(sum(r['lean_seconds']for r in allreceipts)-scope['all_retained_lean_seconds'])<1e-8
result={'scope':'Public census/generation/source and preserved failed history; no new verifier invocation','modules':100,'explicit_public_declarations':842,'pins_rehashed':len(checked),'sealed_selected_leaf_mixture_matches_parent_replay':True,'root54_seven_sources_match_parent_regeneration':True,'additional_exact_regenerations':reg,'link57_successor_delta':'Only omit unused CharP on copy_of_truth; all other template bytes identical','retained_receipts':400,'failed_history':failed,'failed_attempts':13,'failed_kernel_acceptance':0,'all_failed_cleanup_clean':True,'full_transfer':'OPEN'}
(J/'source-history-review01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items()if k not in ['failed_history','additional_exact_regenerations']}))
