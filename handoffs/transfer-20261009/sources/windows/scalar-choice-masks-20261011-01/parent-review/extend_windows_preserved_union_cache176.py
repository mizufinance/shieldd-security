"""Extend exact independently reviewed associations after verified publication; no replay."""
from pathlib import Path
import json,hashlib,subprocess,argparse
J=Path(__file__).parent;G=J.parent/'shared-build-handoff'
p=argparse.ArgumentParser();p.add_argument('prior');p.add_argument('label');p.add_argument('module');p.add_argument('count',type=int);p.add_argument('output');a=p.parse_args()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
D=J/('windows-'+a.label+'-review01');P=D/'packet01';pub=G/'handoffs/transfer-20261009/sources/windows'/(a.label+'-20261011-01')/a.label
if not(P/'qualified/plan.json').exists():
 records=json.loads((pub.parent/'original-byte-map01.json').read_bytes())['files']
 for relative in ['qualified/plan.json','review.json','context/owned-composition-review.json','source/ShielddSecurity/'+a.module+'.lean']:
  original=str(P/relative);record=next(v for v in records if v['original']['path']==original);published=pub.parent/record['publication']['path'];assert published==pub/relative;assert pin(published)['bytes']==record['original']['bytes']and pin(published)['sha256']==record['original']['sha256']
 P=pub
x=json.loads((J/a.prior).read_bytes());r=json.loads((D/'endpoint-audit-review01.json').read_bytes());assert r['status']=='PASSED'and r['fresh_modules']==1 and r['fresh_reports']==a.count ;assert r['ancestry_cache']['sha256']==pin(J/a.prior)['sha256'];plan=json.loads((P/'qualified/plan.json').read_bytes());raw=json.loads((P/'review.json').read_bytes());t=plan['targets'][0];assert t['module']==a.module and a.module not in x['modules'];assert len(raw['compiler_result']['objects'])==1
source=pub/'source/ShielddSecurity'/(a.module+'.lean');assert source.read_bytes()==(P/'source/ShielddSecurity'/(a.module+'.lean')).read_bytes();assert pin(source)['sha256']==t['source']['sha256'];assert not subprocess.check_output(['git','status','--porcelain'],cwd=G,text=True).strip();head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=G,text=True).strip()
owned=json.loads((P/'context/owned-composition-review.json').read_bytes());owned_by_name={e['module']:e for e in owned['selected']}
expected_inherited={k:v for k,v in x['reports'].items()if any(k.startswith('ShielddSecurity.'+n+'.')for n in owned_by_name)};assert owned['inherited_public_reports']==expected_inherited and len(expected_inherited)==r['inherited_reports']
for n,current in owned_by_name.items():
 original=x['modules'][n];assert current['source']==original['source']and all(current['object'][k]==original['object'][k]==current['copy'][k]for k in ['bytes','sha256'])
merged_owned=dict(kind='Root exact union of previously independently accepted original ancestry; consuming endpoint actual subset retained separately, no fresh copy/remote object/replay claim',selected=[dict(module=n,source=e['source'],object=e['object'],scope='Exact original already independently accepted source/object identity; not a new consumer copy')for n,e in sorted(x['modules'].items())],inherited_public_reports=dict(x['reports']),consumer_original_owned=pin(P/'context/owned-composition-review.json'),prior_cache=pin(J/a.prior),full_transfer='OPEN')
merged_path=J/(Path(a.output).stem+'-merged-original-qualification01.json');assert not merged_path.exists();merged_path.write_text(json.dumps(merged_owned,indent=2)+'\n')
x['modules'][a.module]=dict(source=t['source'],object=raw['compiler_result']['objects'][0],local_reviewed_source=str(source));fresh={z['declaration']:{k:z[k]for k in ['axioms','full_type_sha256']}for z in r['full_declarations']};assert len(fresh)==a.count and not(set(fresh)&set(x['reports']));x['reports'].update(fresh)
x.update(review_anchor=pin(D/'endpoint-audit-review01.json'),canonical=head,newest_module=a.module,newest_publication=str(pub.parent),original_qualification={k:pin(pub/f)for k,f in [('plan','qualified/plan.json'),('review','review.json'),('owned','context/owned-composition-review.json')]})
x['original_qualification']['owned']=pin(merged_path)
out=J/a.output
with out.open('x')as f:json.dump(x,f,indent=2);f.write('\n')
print(json.dumps({**pin(out),'modules':len(x['modules']),'reports':len(x['reports'])}))
