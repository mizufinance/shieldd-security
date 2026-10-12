from pathlib import Path
import json,hashlib,lzma
MAP=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-history-metadata-preservation126-43/archive-map01.json')
SHA='e994d6fc233c5b95dd9975d71fdfad31c632a5509b7c1a9528cb4769b8343d23'
TABLE=None
def read_original(path,expected):
 global TABLE
 if TABLE is None:
  b=MAP.read_bytes();assert len(b)==1585505 and hashlib.sha256(b).hexdigest()==SHA;TABLE=json.loads(b)['records']
 p=Path(path);v=TABLE[str(p)];assert str(p).endswith('.stdout')and '/runtime/logs/'in str(p)and v['original']==expected and not p.exists()
 q=Path(v['archive']['path']);assert q.is_file()and not q.is_symlink();raw=q.read_bytes();assert len(raw)==v['archive']['bytes']and hashlib.sha256(raw).hexdigest()==v['archive']['sha256']
 de=lzma.LZMADecompressor(memlimit=128*1024*1024);b=de.decompress(raw,max_length=expected['bytes']+1);assert de.eof and not de.unused_data and len(b)==expected['bytes']and hashlib.sha256(b).hexdigest()==expected['sha256'];return b
