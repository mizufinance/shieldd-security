"""Independent isolated maintained source replay; no Lean invocation."""
from pathlib import Path
import json,shutil,subprocess,hashlib
J=Path(__file__).parent;S=J.parent.parent/'mac-indexed-row-slice63-source01';D=J/'source-replay-fresh';D.mkdir()
for r in json.loads((S/'producer-manifest01.json').read_bytes()).values():
 b=Path(r['path']).read_bytes();assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256']
for n in ['generate.py','template.lean']:shutil.copyfile(S/n,D/n)
r=subprocess.run(['python3','-I','-B','-S',str(D/'generate.py')],capture_output=True);assert r.returncode==0,r.stderr
assert(D/'source-root/ShielddSecurity/CompilerRowSlice63.lean').read_bytes()==(S/'source-root/ShielddSecurity/CompilerRowSlice63.lean').read_bytes()
print('exact maintained source replay')
