"""Isolated exact generator replay against independently pinned predecessor source."""
from pathlib import Path
import hashlib,json,subprocess,shutil
J=Path(__file__).parent
base=J/'windows-index-count-review01/packet01/source/ShielddSecurity/TransferOrdinaryIndexCountSource01.lean'
for label,module in [('count-codec-join','TransferOrdinaryCountCodecJoin01'),('max-count','TransferOrdinaryMaxCount01')]:
 D=J/('windows-'+label+'-review01');P=D/'packet01';T=D/'source-replay01';T.mkdir()
 B=T/'transfer-ordinary-index-count-20261011-01/handwritten';B.mkdir(parents=True);shutil.copyfile(base,B/base.name)
 R=T/'qualified';R.mkdir();shutil.copyfile(P/'qualified/generate.py',R/'generate.py')
 r=subprocess.run(['python3','-I','-B','-S',str(R/'generate.py')],capture_output=True,text=True,timeout=60);assert r.returncode==0,r.stderr
 b=(R/'generated'/(module+'.lean')).read_bytes();assert b==(P/'source/ShielddSecurity'/(module+'.lean')).read_bytes()
 pin=lambda p:dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 out=dict(status='PASSED',kind='Exact isolated maintained generator replay; no Lean execution',module=module,source_bytes=len(b),source_sha256=hashlib.sha256(b).hexdigest(),generator=pin(P/'qualified/generate.py'),input_source=pin(base),full_transfer='OPEN')
 (D/'generator-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
