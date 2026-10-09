"""Append post-run guard identities without a producer-manifest self-reference."""
import hashlib,json
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-width3-08'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=sorted(O.glob('publication-manifest*.json'))[-1];manifest=json.loads(m.read_text())
for entry in manifest['files']:assert sha(R/entry['path'])==entry['sha256'],entry['path']
guards=[p for p in sorted(O.glob('seal-guard*.json')) if json.loads(p.read_text())['status']=='passed'];assert guards
g=guards[-1];d=json.loads(g.read_text());assert sha(g.with_suffix('.log'))==d['log_sha256']
items=[dict(path=str(p.relative_to(R)),sha256=sha(p),bytes=p.stat().st_size,publication=p.suffix!='.log') for p in [m,g,g.with_suffix('.log'),O/'full-call-result01.json',O/'seal-provenance01.json',Path(__file__)]]
e=O/'publication-envelope01.json';assert not e.exists();e.write_text(json.dumps(dict(schema='width3-full65-envelope-v1',producer_manifest_sha256=sha(m),post_run_guard_path=str(g.relative_to(R)),post_run_guard_sha256=sha(g),scope_path=str((O/'full-call-result01.json').relative_to(R)),scope_sha256=sha(O/'full-call-result01.json'),transport_additions=items,seal_verified=True,full_transfer='OPEN'),indent=2)+'\n');print(str(e.relative_to(R)),sha(e))
