from pathlib import Path
import json,hashlib,lzma,re
J=Path(__file__).parent;W=J.parent
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def read(v):
 p=Path(v['path']);assert p.is_file()and not p.is_symlink();b=p.read_bytes();assert len(b)==v['bytes']and hashlib.sha256(b).hexdigest()==v['sha256'];return b
a=W/'mac-history-metadata-preservation126-42/archive-map01.json';p=W/'mac-history-metadata-preservation126-43/archive-map01.json';assert pin(a)['sha256']=='7d7c0fc398cfd90f0e6857a3600e382ddf38f9570d3da2d7a5b189f00f865f23';assert pin(p)['bytes']==1585505 and pin(p)['sha256']=='e994d6fc233c5b95dd9975d71fdfad31c632a5509b7c1a9528cb4769b8343d23'
a=json.loads(a.read_bytes());m=json.loads(p.read_bytes());assert m['prior_map']==pin(Path(m['prior_map']['path']));assert len(a['records'])==761 and len(m['records'])==1827 and all(m['records'][k]==v for k,v in a['records'].items());added={k:v for k,v in m['records'].items()if k not in a['records']};assert len(added)==1066
total=packed=failed=0
for k,v in added.items():
 assert re.fullmatch(re.escape(str(W))+r'/mac-full-arithmetic45-execution[0-9]+/runtime/logs/[0-9]+-[A-Za-z0-9]+\.stdout',k)
 assert not Path(k).exists()and v['original']['path']==k and 0<v['original']['bytes']<=16*1024*1024 and v['mode']==420 and isinstance(v['mtime_ns'],int)
 raw=read(v['archive']);de=lzma.LZMADecompressor(memlimit=128*1024*1024);out=de.decompress(raw,max_length=v['original']['bytes']+1);assert de.eof and not de.unused_data and len(out)==v['original']['bytes']and hashlib.sha256(out).hexdigest()==v['original']['sha256']
 receipt=json.loads(read(v['receipt']));assert receipt['stdout']==v['original']and receipt['status']==v['status']and v['status']in ['passed','failed'];assert receipt['cleanup']['clean'];failed+=v['status']=='failed';total+=len(out);packed+=len(raw)
reader=J/'read_preserved_mac_stdout01.py';assert not reader.exists();reader.write_text('''from pathlib import Path
import json,hashlib,lzma
MAP=Path('''+repr(str(p))+''')
SHA='e994d6fc233c5b95dd9975d71fdfad31c632a5509b7c1a9528cb4769b8343d23'
TABLE=None
def read_original(path,expected):
 global TABLE
 if TABLE is None:
  b=MAP.read_bytes();assert len(b)==1585505 and hashlib.sha256(b).hexdigest()==SHA;TABLE=json.loads(b)['records']
 p=Path(path);v=TABLE[str(p)];assert str(p).endswith('.stdout')and '/runtime/logs/'in str(p)and v['original']==expected and not p.exists()
 q=Path(v['archive']['path']);assert q.is_file()and not q.is_symlink();raw=q.read_bytes();assert len(raw)==v['archive']['bytes']and hashlib.sha256(raw).hexdigest()==v['archive']['sha256']
 de=lzma.LZMADecompressor(memlimit=128*1024*1024);b=de.decompress(raw,max_length=expected['bytes']+1);assert de.eof and not de.unused_data and len(b)==expected['bytes']and hashlib.sha256(b).hexdigest()==expected['sha256'];return b
''')
r=dict(status='PASSED',map=pin(p),prior_records_exact=761,new_original_stdout_records=1066,original_bytes=total,archive_bytes=packed,failed_original_records=failed,reader=pin(reader),scope='Only exact original inactive stdout bytes, receipt/status and lossless bounded archive association reviewed. Existing failed diagnostics remain failed; no new proof or guard qualification. The map42 derived configuration baseline is not approved by this log-only review. No sources/objects/receipts fallback; no Lean execution.',full_transfer='OPEN');out=J/'mac-original-stdout-preservation-review204.json';assert not out.exists();out.write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k]for k in ['status','new_original_stdout_records','original_bytes','archive_bytes','failed_original_records']}))
