"""Exact memoized parsing/storage review; no process launch or worker mutation."""
from pathlib import Path
import ast,hashlib,json,lzma,difflib,re
J=Path(__file__).parent;W=J.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=sha(b))
maps=[W/f'mac-history-metadata-preservation126-{n}/archive-map01.json' for n in [19,20,21]]
expected=['82690ba5a3478f336554e7f519c494ed576a77f55bfc1b295bed78d14dcd073b','6ea499517d29174df8b68150ecc99d76b26b2ca358f4ba7d5ea6db61a7e0cdef','7643813bc061525109dd9b3268b8736a2daddd42cd033ac9920dbeff30a8dbe3']
parsed=[];added=[];configs={}
for p,h in zip(maps,expected):assert pin(p)['sha256']==h;parsed.append(json.loads(p.read_bytes()))
for a,b in zip(parsed,parsed[1:]):
 assert a['schema']==b['schema']=='exact-inactive-configuration-storage01'
 assert all(b['records'][k]==v for k,v in a['records'].items())
 for k,v in b['records'].items():
  if k in a['records']:continue
  orig,arc=v['original'],v['archive'];assert k==orig['path'] and 0<orig['bytes']<=16*1024*1024
  p=Path(arc['path']);assert not p.is_symlink() and pin(p)==arc
  dec=lzma.LZMADecompressor(memlimit=128*1024*1024);data=dec.decompress(p.read_bytes(),max_length=orig['bytes']+1)
  assert dec.eof and not dec.unused_data and len(data)==orig['bytes'] and sha(data)==orig['sha256']
  configs[k]=data;added.append(v)
old=W/'mac-full-arithmetic45-execution208/maintained/guard.py';fresh=W/'mac-full-arithmetic45-execution209/maintained/guard.py'
assert pin(old)['sha256']=='2245839157e8064968f67c2f9e69976b06837b0760f4fce9bc0b7832a060b792'
assert pin(fresh)['sha256']=='695a7423e2ac2ceea3d676a1f658714555ed310eb5f3e19631be490655bf6d55'
before=old.read_text();after=fresh.read_text();e=before.replace(str(maps[0]),str(maps[1])).replace("'bytes': 117560","'bytes': 120024").replace(expected[0],expected[1])
e=e.replace('def official_header(data):','def uncached_official_header(data):')
needle='\ndef source_check(data, spec):'
insert='\n_OFFICIAL_HEADERS={}\ndef official_header(data):\n    digest=sha(data)\n    if digest not in _OFFICIAL_HEADERS:\n        _OFFICIAL_HEADERS[digest]=tuple(uncached_official_header(data))\n    return list(_OFFICIAL_HEADERS[digest])\n\n'
assert e.count(needle)==1;e=e.replace(needle,insert+needle)
needle="    require(official['manifest_count']<=4 and config['official']['bytes']<=16*1024*1024, 'official manifest cap')\n"
assert e.count(needle)==1;e=e.replace(needle,needle+"    admitted_imports={'ShielddSecurity.'+k for k in closure['modules']}|set(official['official_modules'])\n")
e=e.replace("require(all(x in {'ShielddSecurity.'+k for k in closure['modules']}|set(official['official_modules']) for x in declared)","require(all(x in admitted_imports for x in declared)")
assert e==after
assert (W/'mac-full-arithmetic45-execution210/maintained/guard.py').read_text()==after
last=W/'mac-full-arithmetic45-execution211/maintained/guard.py'
assert last.read_text()==after.replace(str(maps[1]),str(maps[2])).replace("'bytes': 120024","'bytes': 121256").replace(expected[1],expected[2])
# Run only parsing/hash functions in memory. Content hashes remain exact cache keys;
# a returned list cannot mutate the cached immutable tuple.
funcs=[n for n in ast.parse(after).body if isinstance(n,ast.FunctionDef) and n.name in {'require','sha','uncached_official_header','official_header'}]
assert len(funcs)==4
env=dict(hashlib=hashlib,re=re,_OFFICIAL_HEADERS={});exec(compile(ast.Module(body=funcs,type_ignores=[]),str(fresh),'exec'),env)
samples=[b'import Init.Data.Nat\n',b'prelude\nimport Init Prelude\n',b'/- hidden import Bad -/\nimport A B\n',b'-- import X\nimport C\n',b'/- a /- nested -/ end -/\nimport D\n']
for b in samples:
 a=env['uncached_official_header'](b);assert env['official_header'](b)==a
 changed=env['official_header'](b);changed.append('Injected');assert env['official_header'](b)==a
 assert env['official_header'](b+b'import New\n')==env['uncached_official_header'](b+b'import New\n')
physical=dict(threads=1,heap_MiB=2048,group_rss_bytes=4294967296,module_seconds=240,minimum_free_RAM_percent=15,minimum_free_disk_bytes=2147483648,heartbeats=900000,recdepth=8192)
cp=[]
for n in [209,210,211]:
 p=W/f'mac-full-arithmetic45-execution{n}/config01.json';data=p.read_bytes() if p.exists() else configs[str(p)];c=json.loads(data)
 assert all(c['limits'][k]==v for k,v in physical.items()) and c['lean_environment']['LEAN_NUM_THREADS']=='1'
 assert 'total_attempts' not in c['limits'] and 'aggregate_lean_seconds' not in c['limits']
 cp.append(dict(path=str(p),bytes=len(data),sha256=sha(data)))
reader=(J/'read_preserved_mac_config08.py').read_text().replace(str(maps[0]),str(maps[2])).replace(expected[0],expected[2]).replace('len(raw) == 117560','len(raw) == 121256')
(J/'read_preserved_mac_config09.py').write_text(reader)
(J/'mac-header-cache-delta209.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True))))
report=dict(status='PASSED',kind='Exact import-header memoization and lossless archive-map20/21 review; no verifier launch',guards=[pin(fresh),pin(last)],same_209_210=True,maps=[pin(p)for p in maps],added_records=len(added),prior_records_exact=True,bounded_archive_size_sha_eof_verified=True,configuration_pins=cp,physical_limits=physical,scope='Only pure parsing cached by exact byte digest, unchanged admitted module set precomputed, inactive config archive pins advanced. All other guard bytes exact; physical limits, one-job/no-replay, identities, full pre/post census and type/axiom audits unchanged.',pure_parse_tests='PASSED; changed content and returned-list mutation cannot reuse another parsed header',full_transfer='OPEN')
(J/'mac-header-cache-guard-review10.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(status='PASSED',guards=report['guards'],added_records=len(added))))
