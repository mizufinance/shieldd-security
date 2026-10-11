"""Review immutable archival-map successors and guard-only constant deltas."""
from pathlib import Path
import ast, hashlib, json, lzma, difflib, importlib.util
J=Path(__file__).parent; W=J.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
baseline=W/'mac-history-metadata-preservation126-13/archive-map01.json'
assert sha(baseline.read_bytes())=='8229d79c5981494de3c4f850f6ee12218518fe804e942abd3e872544e341cea3'
previous=json.loads(baseline.read_bytes()); added=[]
for number,digest in [(14,'630ee1dac41ec5878c9c9b3eb5f317a3c0148f491bee66e0e39ce3a284ba3c0d'),(15,'27c9f9a30f9420ac64033631f626d9087c063ddf943692c18bfe0577f75ac69d')]:
 p=W/f'mac-history-metadata-preservation126-{number}/archive-map01.json';raw=p.read_bytes();assert sha(raw)==digest
 current=json.loads(raw);assert current['schema']==previous['schema']=='exact-inactive-configuration-storage01'
 assert all(current['records'][k]==v for k,v in previous['records'].items())
 for k,r in current['records'].items():
  if k in previous['records']:continue
  original=r['original'];q=Path(r['archive']['path']);source=Path(k)
  assert source.parent.parent==W and source.name=='config01.json' and source.parent.name.removeprefix('mac-full-arithmetic45-execution').isdigit()
  assert original['path']==k and 0<original['bytes']<=16*1024*1024
  assert q.is_file() and not q.is_symlink() and q.parent==p.parent and q.suffix=='.xz'
  b=q.read_bytes();assert len(b)==r['archive']['bytes'] and sha(b)==r['archive']['sha256']
  decoder=lzma.LZMADecompressor(memlimit=128*1024*1024);data=decoder.decompress(b,max_length=original['bytes']+1)
  assert decoder.eof and not decoder.unused_data and len(data)==original['bytes'] and sha(data)==original['sha256'];json.loads(data)
  if source.exists():assert source.read_bytes()==data
  added.append(r)
 previous=current
reader=(J/'read_preserved_mac_config04.py').read_text().replace('preservation126-13','preservation126-15').replace('8229d79c5981494de3c4f850f6ee12218518fe804e942abd3e872544e341cea3','27c9f9a30f9420ac64033631f626d9087c063ddf943692c18bfe0577f75ac69d').replace('len(raw) == 102847','len(raw) == 106543')
(J/'read_preserved_mac_config05.py').write_text(reader)
spec=importlib.util.spec_from_file_location('preserved',J/'read_preserved_mac_config05.py');preserved=importlib.util.module_from_spec(spec);spec.loader.exec_module(preserved)
strip=lambda t:ast.dump(ast.Module(body=[n for n in t.body if not(isinstance(n,ast.Assign)and any(isinstance(x,ast.Name)and x.id=='_STORAGE_PIN' for x in n.targets))],type_ignores=[]),include_attributes=False)
guards=[];prior=W/'mac-full-arithmetic45-execution176/maintained/guard.py';assert sha(prior.read_bytes())=='c89c57b55398743a1206490855d7960630636af66a8208533e85f62a6ac8bf47'
physical={'threads':1,'heap_MiB':2048,'group_rss_bytes':4294967296,'module_seconds':240,'minimum_free_RAM_percent':15,'minimum_free_disk_bytes':2147483648,'heartbeats':900000,'recdepth':8192}
for stage,digest in [(184,'76af92ea7008ad69071c5cb7e2e8458204d6e43c476b68b1babf08e01e518bca'),(186,'6217fe1842defd749fbe03e34a46024234156c16f2a36a15ca58824b845c218c')]:
 p=W/f'mac-full-arithmetic45-execution{stage}/maintained/guard.py';b=p.read_bytes();assert sha(b)==digest
 a,t=ast.parse(prior.read_bytes()),ast.parse(b);assert strip(a)==strip(t)
 pins=[ast.literal_eval(n.value) for n in t.body if isinstance(n,ast.Assign)and any(isinstance(x,ast.Name)and x.id=='_STORAGE_PIN' for x in n.targets)];assert len(pins)==1
 pin=pins[0];data=Path(pin['path']).read_bytes();assert len(data)==pin['bytes'] and sha(data)==pin['sha256']
 config=json.loads(preserved.read_config(p.parent.parent/'config01.json'));assert all(config['limits'][k]==v for k,v in physical.items()) and config['lean_environment']['LEAN_NUM_THREADS']=='1'
 guards.append({'guard':{'path':str(p),'bytes':len(b),'sha256':digest},'baseline_sha256':sha(prior.read_bytes()),'storage_map':pin,'only_storage_constant_changed':True})
 (J/f'pending-mac-archived-metadata-guard-delta{stage}.diff').write_text(''.join(difflib.unified_diff(prior.read_text().splitlines(True),p.read_text().splitlines(True),fromfile=str(prior),tofile=str(p))))
 prior=p
out={'status':'PASSED','scope':'Source/metadata review only; no verifier launch','guards':guards,'physical_limits':physical,'latest_map_records':len(previous['records']),'prior167_records_unchanged':True,'new_original_records':added,'new_original_bytes':sum(r['original']['bytes']for r in added),'review':'Every guard statement except the precise immutable storage-map assignment remains AST-identical; immutable maps extend prior exact records. Additional original inactive configs reproduced under bounded size/hash/EOF checks. Machine controls unchanged.','full_transfer':'OPEN'}
(J/'mac-archived-metadata-successors-review04.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps({k:out[k]for k in ['status','latest_map_records','new_original_bytes']}))
