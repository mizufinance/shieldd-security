from pathlib import Path
import hashlib,json
J=Path(__file__).parent;W=J.parent;S=W/'mac-official-cache277-restoration03'
def pin(p):
 p=Path(p);assert p.is_file()and not p.is_symlink();h=hashlib.sha256()
 with p.open('rb')as f:
  while b:=f.read(1024*1024):h.update(b)
 return dict(path=str(p),bytes=p.stat().st_size,sha256=h.hexdigest())
def read(v):assert pin(v['path'])==v;return json.loads(Path(v['path']).read_bytes())
planpath=W/'mac-official-cache277-restoration01/plan01.json';assert pin(planpath)['sha256']=='aed8a7d8c53580dc7c8162522ff467d6833e459e8fcc50e75bca89cfa0436fed';plan=json.loads(planpath.read_bytes());old=read(plan['old_official_manifest']);assert old['revisions']['mathlib']=='c5ea00351c28e24afc9f0f84379aa41082b1188f'
resultpath=S/'result01.json';assert pin(resultpath)['sha256']=='bb5e93858fe237ba660ed94067ecac35e06d081472968c5cf886df82f29d3339';result=json.loads(resultpath.read_bytes())
assert result['status']=='EXACT_OFFICIAL_CACHE_RESTORED_NO_LEAN' and result['modules']==len(result['records'])==len(plan['records'])==627
assert result['old_manifest']==plan['old_official_manifest'];objects={};modules=[]
def key(path):return path.split('/.lake/packages/',1)[1]
for i,(planned,actual)in enumerate(zip(plan['records'],result['records'],strict=True)):
 assert planned['module']==actual['module'];modules.append(actual['module'])
 assert pin(planned['archive']['path'])==planned['archive'];assert pin(planned['source']['path'])==planned['source']
 assert old['files'][key(planned['source']['path'])]==planned['source']['sha256']
 wanted={v['path']:v['sha256']for v in planned['wanted'].values()if v['sha256']is not None}
 assert set(actual['objects'])==set(wanted)and len(wanted)==4
 for path,v in actual['objects'].items():
  assert path==v['path']and path not in objects and v['sha256']==wanted[path]==old['files'][key(path)]
  assert pin(path)==v;objects[path]=v
 for v in planned['wanted'].values():
  if v['sha256']is None:assert not Path(v['path']).exists()and not Path(v['path']).is_symlink()
 receipt=json.loads((S/'runtime'/f'restored-{i:04d}.json').read_bytes())
 assert receipt['module']==actual['module']and receipt['input_archive']==planned['archive']and receipt['source']==planned['source']and receipt['objects']==actual['objects']
 assert type(receipt['exit'])is int and receipt['exit']==0 and receipt['cleanup']['clean']is True and receipt['cleanup']['leader_reaped']is True
 assert receipt['peak_group_rss']<=4*1024**3 and receipt['elapsed']<=240
 cmd=receipt['command'];assert cmd[0]==plan['tool']['path']and cmd[1:4]==['-x','--jobs','1']
 assert (S/'runtime'/f'extract-{i:04d}.stderr').read_bytes()==b'' and (S/'runtime'/f'extract-{i:04d}.stdout').stat().st_size<=65536
 assert not (S/'runtime'/f'scratch-{i:04d}').exists()
assert len(set(modules))==627 and len(objects)==2508 and sum(v['bytes']for v in objects.values())==result['physical_restored_bytes']==417098969
# Source-only, immutable original failure/partial output records remain exact.
envelope=json.loads((S/'source-envelope01.json').read_bytes());assert len(envelope['existing_original_outputs'])==1
for v in envelope['preserved_partial_files'].values():assert pin(v['path'])==v
for v in envelope['existing_original_outputs'].values():assert pin(v['path'])==v
report=dict(status='PASSED',result=pin(resultpath),plan=pin(planpath),old_manifest=plan['old_official_manifest'],modules=627,objects=2508,physical_restored_bytes=417098969,scope='Every restored source/kernel companion matched the older exact-pinned Mathlib/package official manifest and current physical bytes; all627 original serial extraction receipts/cleanup and streams checked.627 distinct modules,2508 unique companions; unselected .ir stayed absent. Original failed/partial restoration02 remains intact, only one preinstalled .ilean explicitly corrected. Official cache restoration only, no new Lean declaration/type/axiom qualification or full Transfer closure.',full_transfer='OPEN')
out=J/'mac-official-restoration-review323.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print('PASSED627 modules2508 exact official objects417098969B; no Lean qualification')
