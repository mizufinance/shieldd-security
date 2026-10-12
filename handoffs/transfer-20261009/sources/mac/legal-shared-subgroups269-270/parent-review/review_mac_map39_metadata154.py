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
old=W/'mac-history-metadata-preservation126-38/archive-map01.json'
new=W/'mac-history-metadata-preservation126-39/archive-map01.json'
assert pin(old)['sha256']=='bc968e33d496fe9f4257c83c02f81422f80e727c5af56b8df6853c68649c9001'
assert pin(new)['bytes']==478174 and pin(new)['sha256']=='ed8adb7a117339309544f67282bd2a2e7d25c8090a3994ec2d973340b64a94c8'
a=strict(old.read_bytes()); b=strict(new.read_bytes()); prior=a['records']; records=b['records']
assert a['schema']==b['schema']=='exact-inactive-phase-metadata-storage02'
assert len(prior)==736 and len(records)==745 and all(records[k]==v for k,v in prior.items())
added={k:v for k,v in records.items() if k not in prior}; assert len(added)==9
total=packed=0
for k,v in added.items():
 assert re.fullmatch(re.escape(str(W))+r'/mac-full-arithmetic45-execution28[7-9]/(config01|protected-history01|overlay-manifest01)\.json',k)
 o=v['original']; ar=v['archive']; p=Path(ar['path'])
 assert o['path']==k and 0<o['bytes']<=16*1024*1024 and p.is_file() and not p.is_symlink() and not Path(k).exists()
 raw=p.read_bytes(); assert len(raw)==ar['bytes'] and hashlib.sha256(raw).hexdigest()==ar['sha256']
 dec=lzma.LZMADecompressor(memlimit=128*1024*1024); out=dec.decompress(raw,max_length=o['bytes']+1)
 assert dec.eof and not dec.unused_data and len(out)==o['bytes'] and hashlib.sha256(out).hexdigest()==o['sha256']
 assert isinstance(strict(out),dict) and v['mode']==420 and isinstance(v['mtime_ns'],int)
 total+=len(out); packed+=len(raw)
bp=pin(old);sp=pin(new)
reader=J/'read_preserved_mac_config16.py'; assert not reader.exists()
raw=(J/'read_preserved_mac_config15.py').read_text().replace('preservation126-38','preservation126-39').replace(bp['sha256'],sp['sha256']).replace('472324','478174')
reader.write_text(raw)
spec=importlib.util.spec_from_file_location('reviewed_reader16',reader); module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
configs=0
for k,v in added.items():
 assert pin(Path(v['archive']['path']))==v['archive']
 original=module.read_original(k,v['original']); assert len(original)==v['original']['bytes']
 if k.endswith('/config01.json'):
  effective=module.read_config(k); wrapper=strict(original)
  if wrapper.get('schema')=='bounded-pinned-execution-delta01':
   assert len(effective)==wrapper['effective_bytes'] and hashlib.sha256(effective).hexdigest()==wrapper['effective_sha256']
  configs+=1
out=J/'mac-storage-map39-review154.json'; assert not out.exists()
report=dict(status='PASSED',baseline_map=pin(old),successor_map=pin(new),prior_records_exact=736,new_records_exact=9,new_original_bytes=total,new_archive_bytes=packed,config_reconstructions=configs,reader=pin(reader),prior_guard_review=pin(J/'mac-carried-history-cache-guard-review28.json'),scope='All 9 append-only inactive metadata records bounded lossless raw identities and effective configs reviewed; prior736 records exactly unchanged. No guard approval or verifier execution inferred from archiving. No sources, objects or receipts fallback; no Lean or guard execution.',full_transfer='OPEN')
out.write_text(json.dumps(report,indent=2)+'\n'); print(json.dumps({k:report[k] for k in ['status','new_records_exact','new_original_bytes','new_archive_bytes','config_reconstructions']}))
