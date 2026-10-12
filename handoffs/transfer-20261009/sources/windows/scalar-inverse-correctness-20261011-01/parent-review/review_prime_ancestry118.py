"""Bind a previously accepted prime tree to exact original source/object/report identities.
No compilation, proof replay, or fresh remote object observation is claimed.
"""
from pathlib import Path
import json,hashlib,re,tarfile,subprocess
J=Path(__file__).parent;G=J.parent/'shared-build-handoff';D=G/'handoffs/transfer-20261009/sources/windows/field-cardinality-20261010-02';R=J/'windows-field-cardinality-review01'
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=sha(b))
assert not subprocess.check_output(['git','status','--porcelain'],cwd=G,text=True).strip()
pub=json.loads((D/'publication-manifest01.json').read_text());tracked=0
for name,v in pub['files'].items():
 p=D/name;b=p.read_bytes();assert len(b)==v['bytes'] and sha(b)==v['sha256']
 assert subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(G))],cwd=G)==b;tracked+=1
audit=json.loads((D/'parent-review/audit-result01.json').read_text());assert audit['manifest_files_rehashed']==160 and len(audit['modules'])==48 and audit['declarations']==167
verification=json.loads((D/'parent-review/transport-verification01.json').read_text());arc=R/'transport01.tar.xz';a=pin(arc);assert a['bytes']==verification['archive_bytes']==82332 and a['sha256']==verification['archive_sha256']=='95306c503a4c36027919716ff75fd4766301772c85d193d3a9678730c7f8f3cc'
with tarfile.open(arc,'r:xz')as t:
 members=t.getmembers();assert all(x.isfile()and not x.name.startswith('/')and '..'not in Path(x.name).parts for x in members)
 assert len(members)<256 and sum(x.size for x in members)<16*1024*1024
 data={m.name:t.extractfile(m).read()for m in members}
manifest=json.loads(data['manifest.json']);assert data['manifest.json']==(D/'manifest.json').read_bytes()
for v in manifest['files']:
 b=data[v['path']];assert len(b)==v['bytes'] and sha(b)==v['sha256']
qualified=json.loads(data['receipts/qualified-modules.json']);assert data['receipts/qualified-modules.json']==(D/'receipts/qualified-modules.json').read_bytes()
names={'ModularPower','LucasCertificate',*[f'FieldPrimeNode{i:02d}'for i in range(1,39)]};selected={e['module']:e for e in qualified if e['module']in names};old={e['module']:e for e in audit['modules']};assert set(selected)==names
modules={};reports={}
for name,e in selected.items():
 r=e['receipt'];assert r['status']=='passed' and 0<r['seconds']<240 and r['peak_rss_bytes']<=4294967296 and len(r['objects'])==1
 assert old[name]['source']==e['source']
 paths=[p for p in D.glob('*/ShielddSecurity/'+name+'.lean')];assert len(paths)==1;p=paths[0];b=p.read_bytes();assert len(b)==e['source']['bytes']and sha(b)==e['source']['sha256'];source=b.decode()
 declared=re.findall(r'^#check @([\w.]+)\s*$',source,re.M);assert len(declared)==len(set(declared)) and declared==[z['name']for z in old[name]['audits']] and set(declared)==set(r['audits'])
 log=data[f'audit-output/{name}.txt'];assert len(log)==r['stdout']['bytes']and sha(log)==r['stdout']['sha256'];text=log.decode();assert not re.search(r'\b(?:warning|error|info|trace):|sorryAx',text)
 for z in old[name]['audits']:
  n=z['name'];matches=list(re.finditer(r"(?m)^@?"+re.escape(n)+r"(?:\.\{[^\n]*?\})?\s*:[\s\S]*?^'"+re.escape(n)+r"' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text));assert len(matches)==1
  m=matches[0];full=m.group(0).split("\n'"+n+"' ",1)[0];axioms=[x.strip()for x in(m.group(1)or'').split(',')if x.strip()]
  assert full==z['full_type']and axioms==z['axioms']and set(axioms)<={'propext','Classical.choice','Quot.sound'}
  report=dict(axioms=axioms,full_type_sha256=sha(full.encode()));assert r['audits'][n]==report;reports[n]=report
 modules[name]=dict(source=e['source'],object=r['objects'][0],local_reviewed_source=str(p),original_qualification=e,original_full_declarations=old[name]['audits'])
assert len(modules)==40 and len(reports)==126
root=next(x for x in old['FieldPrimeNode38']['audits']if x['name'].endswith('.prime'))['full_type'];assert 'Nat.Prime' in root and '52435875175126190479447740508185965837690552500527637822603658699938581184513' in root
out=J/'windows-prime-original-ancestry-supplement118.json';assert not out.exists()
result=dict(status='PASSED',kind='Exact original previously reviewed prime-tree ancestry; no verifier replay or fresh native/object claim',canonical=subprocess.check_output(['git','rev-parse','HEAD'],cwd=G,text=True).strip(),modules=modules,reports=reports,original_review=pin(D/'parent-review/audit-result01.json'),original_qualification=pin(D/'receipts/qualified-modules.json'),original_publication_manifest=pin(D/'publication-manifest01.json'),original_archive=a,tracked_publication_files_rehashed=tracked,original_manifest_files_rehashed=160,scope='Forty exact original modules/126 full standard-axiom reports available for ancestry reuse. Actual remote copied object/source identities must match at the consuming endpoint. Numerical field modulus prime is proved; concrete inverse/native/group/cardinality/full Transfer obligations remain separate.',full_transfer='OPEN')
out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status='PASSED',modules=40,reports=126,tracked_files=tracked,original_files=160,fresh_replay='NONE')))
