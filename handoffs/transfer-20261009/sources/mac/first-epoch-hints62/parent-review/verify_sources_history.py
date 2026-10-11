"""Replay the maintained hint constructor source and retain failed provenance."""
from pathlib import Path
import json,hashlib,re,shutil,subprocess
J=Path(__file__).parent;W=J.parent.parent;P=W/'mac-first-epoch-hints62-kernel-result01';S=W/'mac-first-epoch-hints62-source03';checked={}
def read(r):
 p=Path(r['path']);b=p.read_bytes();assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'];checked[str(p)]=r;return b
for r in json.loads((S/'producer-manifest01.json').read_bytes()).values():read(r)
d=J/'source-replay02';d.mkdir();shutil.copyfile(S/'generate.py',d/'generate.py');shutil.copyfile(S/'template.lean',d/'template.lean')
r=subprocess.run(['python3','-I','-B','-S',str(d/'generate.py')],capture_output=True);assert r.returncode==0,r.stderr
assert (d/'source-root/ShielddSecurity/CapturedEpochHints62.lean').read_bytes()==(S/'source-root/ShielddSecurity/CapturedEpochHints62.lean').read_bytes()
p=json.loads((P/'predecessors01.json').read_bytes());receipt=json.loads(read(p['failed_receipt']));assert receipt['status']=='failed' and receipt['exit']!=0 and receipt['cleanup']['clean'];assert p['fresh_kernel_credit']==0
assert receipt['source']==p['failed_source']and receipt['stdout']==p['stdout']and receipt['stderr']==p['stderr']
for k in ['failed_source','stdout','stderr']:read(p[k])
for producer in p['source_only_producers']:
 for r in json.loads(read(producer)).values():read(r)
a=(W/'mac-first-epoch-hints62-source02/template.lean').read_bytes();b=(S/'template.lean').read_bytes();assert a.replace('rw [←same]'.encode(),b'rw [same]')==b
source=(S/'source-root/ShielddSecurity/CapturedEpochHints62.lean').read_text();names=re.findall(r'^#check @([\w.]+)$',source,re.M);assert len(names)==15 and names==re.findall(r'^#print axioms ([\w.]+)$',source,re.M)
out=dict(kind='Independent exact isolated generator replay and source-first failed provenance; no Lean invocation',source_replay_exact=True,declarations=15,pins_rehashed=len(checked),failed_attempts=1,failed_cleanup_clean=True,source_only_predecessors=2,selected_fix='One List range membership rewrite direction; model definitions and theorem statements unchanged from source02',premises='Canonical soundness uses independent n<p and field meaning, never desired64-bit bound. Construction uses bounded input/guard and explicitly constructed arithmetic satisfaction plus hint agreement. Native/input-recovery connection remains open.',full_transfer='OPEN')
(J/'source-history-review01.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
