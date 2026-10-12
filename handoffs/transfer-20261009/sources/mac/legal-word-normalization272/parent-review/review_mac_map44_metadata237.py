from pathlib import Path
import json,hashlib,lzma,re,importlib.util
J=Path(__file__).parent;W=J.parent
pin=lambda p:dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
a=W/'mac-history-metadata-preservation126-43/archive-map01.json';b=W/'mac-history-metadata-preservation126-44/archive-map01.json'
assert pin(a)['sha256']=='e994d6fc233c5b95dd9975d71fdfad31c632a5509b7c1a9528cb4769b8343d23';assert pin(b)['bytes']==1595150 and pin(b)['sha256']=='9808b44e240eca4e8372cb8929c9993eab67a00ef6ed9fea833e56cbce45d401'
def strict(raw):
 def pairs(v):
  out={}
  for k,x in v:assert k not in out;out[k]=x
  return out
 return json.loads(raw,object_pairs_hook=pairs)
old=strict(a.read_bytes());new=strict(b.read_bytes());assert old['schema']==new['schema']=='exact-inactive-phase-metadata-storage02';assert len(old['records'])==1827 and len(new['records'])==1842 and all(new['records'][k]==v for k,v in old['records'].items());added={k:v for k,v in new['records'].items()if k not in old['records']};total=packed=0
for k,v in added.items():
 assert re.fullmatch(re.escape(str(W))+r'/mac-full-arithmetic45-execution29[5-9]/(config01|protected-history01|overlay-manifest01)\.json',k)
 o=v['original'];ar=v['archive'];p=Path(ar['path']);assert o['path']==k and 0<o['bytes']<=16*1024*1024 and not Path(k).exists() and p.is_file() and not p.is_symlink();raw=p.read_bytes();assert pin(p)==ar;dec=lzma.LZMADecompressor(memlimit=128*1024*1024);out=dec.decompress(raw,max_length=o['bytes']+1);assert dec.eof and not dec.unused_data and len(out)==o['bytes'] and hashlib.sha256(out).hexdigest()==o['sha256'];assert isinstance(strict(out),dict)and v['mode']==420 and isinstance(v['mtime_ns'],int);total+=len(out);packed+=len(raw)
reader=J/'read_preserved_mac_config20.py';assert not reader.exists();reader.write_text((J/'read_preserved_mac_config19.py').read_text().replace('preservation126-43','preservation126-44').replace(pin(a)['sha256'],pin(b)['sha256']).replace('1585505','1595150'))
spec=importlib.util.spec_from_file_location('reader20',reader);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);configs=0
for k,v in added.items():
 assert len(m.read_original(k,v['original']))==v['original']['bytes']
 if k.endswith('/config01.json'):m.read_config(k);configs+=1
report=dict(status='PASSED',baseline_map=pin(a),successor_map=pin(b),prior_records_exact=1827,new_records_exact=15,new_original_bytes=total,new_archive_bytes=packed,config_reconstructions=configs,reader=pin(reader),scope='All fifteen exact inactive phase295..299 original metadata archives independently bounded decompressed/hashed, previous1827 records unchanged. Five effective configurations reconstructed. No physical verifier or guard executed; sources/objects/receipts have no fallback. Guard successor not claimed by this storage review.',full_transfer='OPEN');out=J/'mac-storage-map44-review237.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print({k:report[k]for k in ['status','new_original_bytes','new_archive_bytes','config_reconstructions']})
