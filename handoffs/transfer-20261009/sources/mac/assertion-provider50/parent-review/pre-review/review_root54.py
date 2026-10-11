from pathlib import Path
import hashlib,json,re,subprocess,shutil
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
P=W/'mac-assertion-root54-source01';J=W/'resumed-orchestration-20261009-01/assertion-provider50-pre-review01'
def pin(p):
 assert p.is_file()and not p.is_symlink(),p
 b=p.read_bytes();return {'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def check(p,v):assert pin(p)=={k:v[k]for k in ['bytes','sha256']},p
before={str(p.relative_to(P)):pin(p)for p in P.rglob('*')if p.is_file()}
for n,v in json.loads((P/'producer-manifest01.json').read_bytes()).items():check(P/n,v)
for n in ['envelope01.json','postseal-guard01.json']:
 for k,v in json.loads((P/n).read_bytes()).items():
  if isinstance(v,dict)and 'path'in v:check(Path(v['path']),v)
q=json.loads((W/'mac-assertion-provider50-source01/qualification01.json').read_bytes());wanted={f"CapturedAssertions50B{c['index']:04d}":c['count']for c in q['chunks']}
assert len(wanted)==90
position=177954
for c in q['chunks']:assert c['start']==position;position+=c['count']
assert position==200770
generation=json.loads((P/'generation01.json').read_bytes());groups={};composition={}
for v in generation['outputs']:
 source=Path(v['source']['path']);check(source,v['source']);text=source.read_text()
 m=re.search(r'^noncomputable def block : Block p copy (\d+) := (.+)$',text,re.M);assert m
 ts=re.findall(r'[()]|[A-Za-z0-9_.]+',m[2]);cursor=0
 def parse():
  global cursor
  token=ts[cursor];cursor+=1
  if token=='(':
   assert ts[cursor:cursor+3]==['CompilerAssertionBlock51.append','p','copy'];cursor+=3
   l,r=int(ts[cursor]),int(ts[cursor+1]);cursor+=2
   a,n=parse();b,k=parse();assert (l,r)==(n,k) and ts[cursor]==')';cursor+=1
   return a+b,n+k
  assert token.endswith('.block');name=token[:-6]
  if name in wanted:return [name],wanted[name]
  assert name in groups;return groups[name]
 leaves,count=parse();assert cursor==len(ts)and count==int(m[1])==v['length']
 if v['name']=='CapturedFullAssertions54':assert leaves==list(wanted)and count==22816
 groups[v['name']]=(leaves,count);composition[v['name']]={'leaves':leaves,'count':count,'source':pin(source)}
 assert re.findall(r'^#check @(\S+)$',text,re.M)==v['audits']
 assert re.findall(r'^#print axioms (\S+)$',text,re.M)==v['audits']
 assert len(v['audits'])==(5 if v['name']=='CapturedFullAssertions54'else 1)
R=J/'root54-regeneration01';assert not R.exists();R.mkdir()
for n in ['generate.py','template.lean']:shutil.copyfile(P/n,R/n)
r=subprocess.run(['python3','-I','-B','-S',str(R/'generate.py')],capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stderr
for v in generation['outputs']:check(R/'source-root/ShielddSecurity'/(v['name']+'.lean'),v['source'])
assert before=={str(p.relative_to(P)):pin(p)for p in P.rglob('*')if p.is_file()}
result={'scope':'Independent source composition/order/byte replay only; no kernel acceptance','modules':len(composition),'public_reports_expected':11,'leaf_sources':90,'ordered_rows':22816,'first_original_position':177954,'last_original_position':200769,'all_parent_seal_pins_match':True,'producer_unchanged':True,'sources_byte_exact_regenerated':True,'composition':composition,'residuals':['Field/CharP and copy linkage remain in root54 equivalence; prepared links57 derives copy linkage from actual row','Recorded expression equality is not independent legal-input assertion truth','No 262144-domain padding or native verifier refinement']}
(J/'root54-source-review01.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k!='composition'}))
