from pathlib import Path
import ast, hashlib, json, lzma, re, importlib.util
J=Path(__file__).parent; W=J.parent
def pin(p):
 b=p.read_bytes(); return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def strict(b):
 def unique(ps):
  d={}
  for k,v in ps: assert k not in d; d[k]=v
  return d
 return json.loads(b,object_pairs_hook=unique)
old=W/'mac-history-metadata-preservation126-36/archive-map01.json'
new=W/'mac-history-metadata-preservation126-37/archive-map01.json'
assert pin(old)['sha256']=='81c81ba612d2f180118faec0b4d1fd9b5212d0d4df8508964f4ac472fcc5f407'
assert pin(new)['bytes']==464471 and pin(new)['sha256']=='c200981f686cb8677ed63e0b55138a17bbb57d9dd8234d8cef4e7571ccb533d5'
a=strict(old.read_bytes()); b=strict(new.read_bytes()); prior=a['records']; records=b['records']
assert a['schema']==b['schema']=='exact-inactive-phase-metadata-storage02'
assert len(prior)==661 and len(records)==724 and all(records[k]==v for k,v in prior.items())
added={k:v for k,v in records.items() if k not in prior}; assert len(added)==63
total=packed=0
for k,v in added.items():
 assert re.fullmatch(re.escape(str(W))+r'/mac-full-arithmetic45-execution(26[0-9]|27[0-9]|28[0-2])/(config01|protected-history01|overlay-manifest01)\.json',k)
 o=v['original']; ar=v['archive']; p=Path(ar['path'])
 assert o['path']==k and 0<o['bytes']<=16*1024*1024 and p.is_file() and not p.is_symlink() and not Path(k).exists()
 raw=p.read_bytes(); assert len(raw)==ar['bytes'] and hashlib.sha256(raw).hexdigest()==ar['sha256']
 dec=lzma.LZMADecompressor(memlimit=128*1024*1024); out=dec.decompress(raw,max_length=o['bytes']+1)
 assert dec.eof and not dec.unused_data and len(out)==o['bytes'] and hashlib.sha256(out).hexdigest()==o['sha256']
 assert isinstance(strict(out),dict) and v['mode']==420 and isinstance(v['mtime_ns'],int)
 total+=len(out); packed+=len(raw)
baseline=W/'mac-carried-proof-cache249-source01/guard.py'; successor=W/'mac-full-arithmetic45-execution284/maintained/guard.py'
assert pin(baseline)['sha256']=='e1e43ace6927b7e3fe3904c69322be5fd6f62fcfe8839c5e75b97f418a394fa9'
assert pin(successor)['sha256']=='d38270306c68c5353fe12a9433a67cf02793c1fd1be75593e2a8a40e94004d9a'
def split(p):
 t=ast.parse(p.read_text()); pins=[]; rest=[]
 for n in t.body:
  if isinstance(n,ast.Assign) and any(isinstance(v,ast.Name) and v.id=='_STORAGE_PIN' for v in n.targets): pins.append(ast.literal_eval(n.value))
  else: rest.append(ast.dump(n,include_attributes=False))
 assert len(pins)==1; return pins[0],rest
bp,ba=split(baseline); sp,sa=split(successor); assert ba==sa and bp==pin(old) and sp==pin(new)
reader=J/'read_preserved_mac_config14.py'; assert not reader.exists()
raw=(J/'read_preserved_mac_config13.py').read_text().replace('preservation126-36','preservation126-37').replace(bp['sha256'],sp['sha256']).replace('423587','464471')
reader.write_text(raw)
spec=importlib.util.spec_from_file_location('reviewed_reader14',reader); module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
configs=0
for k,v in added.items():
 assert pin(Path(v['archive']['path']))==v['archive']
 original=module.read_original(k,v['original']); assert len(original)==v['original']['bytes']
 if k.endswith('/config01.json'):
  effective=module.read_config(k); wrapper=strict(original)
  if wrapper.get('schema')=='bounded-pinned-execution-delta01':
   assert len(effective)==wrapper['effective_bytes'] and hashlib.sha256(effective).hexdigest()==wrapper['effective_sha256']
  configs+=1
out=J/'mac-storage-map37-pin-review115.json'; assert not out.exists()
report=dict(status='PASSED',baseline_guard=pin(baseline),successor_guard=pin(successor),baseline_map=pin(old),successor_map=pin(new),prior_records_exact=661,new_records_exact=63,new_original_bytes=total,new_archive_bytes=packed,config_reconstructions=configs,reader=pin(reader),prior_guard_review=pin(J/'mac-carried-history-cache-guard-review28.json'),scope='Only exact storage pin changed; every other top-level AST including all verifier, admission, physical safety, cleanup, archive and memoization code identical. All 63 additions bounded lossless raw identities and effective configs reviewed. No sources, objects or receipts fallback; no Lean or guard execution.',full_transfer='OPEN')
out.write_text(json.dumps(report,indent=2)+'\n'); print(json.dumps({k:report[k] for k in ['status','new_records_exact','new_original_bytes','new_archive_bytes','config_reconstructions']}))
