"""Exact inactive phase metadata preservation and guard delta review; no verifier launch."""
from pathlib import Path
import ast,hashlib,json,lzma,re,difflib
J=Path(__file__).parent;W=J.parent;sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=sha(b))
a=W/'mac-history-metadata-preservation126-21/archive-map01.json';b=W/'mac-history-metadata-preservation126-28/archive-map01.json'
assert pin(a)['sha256']=='7643813bc061525109dd9b3268b8736a2daddd42cd033ac9920dbeff30a8dbe3'
assert pin(b)==dict(path=str(b),bytes=268296,sha256='8807bbd8d63d13a5d6e3085cee3b0707c0e3b96b8ccbcf8b06c41571eee5a92a')
old,new=json.loads(a.read_bytes()),json.loads(b.read_bytes());assert old['schema']=='exact-inactive-configuration-storage01' and new['schema']=='exact-inactive-phase-metadata-storage02'
assert all(new['records'][k]==v for k,v in old['records'].items());added={k:v for k,v in new['records'].items()if k not in old['records']};decoded={};counts={}
for k,v in added.items():
 assert re.fullmatch(re.escape(str(W))+r'/mac-full-arithmetic45-execution[0-9]+/(?:config01|protected-history01)\.json',k)
 orig,arc=v['original'],v['archive'];assert k==orig['path']and 0<orig['bytes']<=16*1024*1024
 p=Path(arc['path']);assert not p.is_symlink()and pin(p)==arc and arc['bytes']<=16*1024*1024
 dec=lzma.LZMADecompressor(memlimit=128*1024*1024);data=dec.decompress(p.read_bytes(),max_length=orig['bytes']+1);assert dec.eof and not dec.unused_data and len(data)==orig['bytes']and sha(data)==orig['sha256']
 if Path(k).exists():assert Path(k).read_bytes()==data
 if k.endswith('/config01.json'):decoded[k]=data
 counts[Path(k).name]=counts.get(Path(k).name,0)+1
base=W/'mac-full-arithmetic45-execution211/maintained/guard.py';prior=base.read_text();pins=[]
def storage(text):
 n=next(n for n in ast.parse(text).body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='_STORAGE_PIN'for t in n.targets));return ast.literal_eval(n.value)
prior_pin=storage(prior)
for n in range(212,216):
 p=W/f'mac-full-arithmetic45-execution{n}/maintained/guard.py';s=p.read_text();mp=storage(s);assert pin(Path(mp['path']))==mp
 assert s==prior.replace(str(prior_pin['path']),mp['path']).replace(str(prior_pin['bytes']),str(mp['bytes'])).replace(prior_pin['sha256'],mp['sha256']);pins.append(pin(p))
fresh=W/'mac-full-arithmetic45-execution216/maintained/guard.py';s=fresh.read_text();mp=storage(s);assert mp==pin(b)
e=prior.replace(str(a),str(b)).replace('121256','268296').replace(pin(a)['sha256'],pin(b)['sha256'])
e=e.replace('# Bounded lossless storage of inactive configuration JSON; proof inputs unchanged.','# Bounded lossless storage of inactive configuration/history JSON; proof inputs unchanged.').replace('exact-inactive-configuration-storage01','exact-inactive-phase-metadata-storage02').replace('config01\\.json','(?:config01|protected-history01)\\.json').replace('only inactive historical config storage','only exact inactive historical phase JSON storage');assert e==s;pins.append(pin(fresh))
physical=dict(threads=1,heap_MiB=2048,group_rss_bytes=4294967296,module_seconds=240,minimum_free_RAM_percent=15,minimum_free_disk_bytes=2147483648,heartbeats=900000,recdepth=8192)
configs=[]
for n in range(212,217):
 p=W/f'mac-full-arithmetic45-execution{n}/config01.json';data=p.read_bytes()if p.exists()else decoded[str(p)];c=json.loads(data);assert all(c['limits'][k]==v for k,v in physical.items())and c['lean_environment']['LEAN_NUM_THREADS']=='1';assert 'total_attempts'not in c['limits']and 'aggregate_lean_seconds'not in c['limits'];configs.append(dict(path=str(p),bytes=len(data),sha256=sha(data)))
reader=(J/'read_preserved_mac_config09.py').read_text().replace(str(a),str(b)).replace(pin(a)['sha256'],pin(b)['sha256']).replace('len(raw) == 121256','len(raw) == 268296').replace('exact-inactive-configuration-storage01','exact-inactive-phase-metadata-storage02').replace('historical configuration bytes','historical configuration/history bytes').replace('archived config map','archived phase metadata map');(J/'read_preserved_mac_config10.py').write_text(reader)
(J/'mac-phase-metadata-delta216.diff').write_text(''.join(difflib.unified_diff(prior.splitlines(True),s.splitlines(True))))
r=dict(status='PASSED',kind='Exact inactive phase metadata archive-map/guard/config review; no verifier/process launch or worker mutation',guards=pins,map=pin(b),prior_records_exact=True,added_records=counts,all_added_bounded_archives_original_size_sha_eof_verified=True,original_added_bytes=sum(v['original']['bytes']for v in added.values()),compressed_added_bytes=sum(v['archive']['bytes']for v in added.values()),configuration_pins=configs,physical_limits=physical,scope='212–215 only immutable map pins advanced.216 only fixed schema/path whitelist extends to inactive protected-history JSON plus pinned map28. Source/object/receipt identities, full historical/fixed/pre/post checks, per-phase cache clearing, one-heavy-job/no-replay/full-type/axiom and physical limits all unchanged.',full_transfer='OPEN');(J/'mac-phase-metadata-guard-review12.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status='PASSED',added=counts,original_bytes=r['original_added_bytes'],compressed_bytes=r['compressed_added_bytes'],guard=pin(fresh))))
