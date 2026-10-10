"""Inspect actual worker receipts and reparse eleven existing outputs; no build."""
import sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
import hashlib,json,runpy
from pathlib import Path
R=Path(__file__).resolve().parents[2];S=R/'work/mac-transfer-cut12';O=R/'outputs/mac-transfer-cut12'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
auditor=S/'audit_log.py'
assert sha(auditor)=='afe6847cae33f7a50c1c049cd07e705c0fe2d24f5eef8880b48c4604aba09a3e'
validate=runpy.run_path(str(auditor))['validate'];results=[]
for name in ['TransferCut12ProbeData01','TransferCut12ProductProbe01']:
 p=O/f'build-{name}-01.json';d=json.loads(p.read_bytes());source=S/'project/ShielddSecurity'/f'{name}.lean';obj=S/'project/.lake/build/lib/lean/ShielddSecurity'/f'{name}.olean';log=p.with_suffix('.log')
 assert d['status']=='passed' and d['exit']==0 and sha(source)==d['source_sha256'] and sha(obj)==d['object_sha256'] and sha(log)==d['log_sha256']
 assert d['timeout_seconds']==240 and d['lean_heap_limit_MiB']==2048 and d['process_group_rss_limit_bytes']==4294967296
 assert d['seconds']<=240 and d['peak_group_rss_bytes']<=4294967296 and d['minimum_memory_free_percent']>=15 and d['minimum_disk_free_bytes']>=2147483648
 parsed=validate(log.read_text(),d['expected_axiom_names'],d['expected_signature_names'])
 assert parsed['axiom_audits']==d['axiom_audits'] and parsed['full_signature_sha256']==d['full_signature_sha256']
 for module,x in d['frozen_imports'].items():
  if not module.startswith('ShielddSecurity.'):continue
  leaf=module.split('.')[-1]
  assert sha(S/'project/ShielddSecurity'/f'{leaf}.lean')==x['source_sha256'] and sha(S/'project/.lake/build/lib/lean/ShielddSecurity'/f'{leaf}.olean')==x['object_sha256']
 results.append(dict(module=name,receipt_sha256=sha(p),source_sha256=sha(source),object_sha256=sha(obj),object_bytes=obj.stat().st_size,seconds=d['seconds'],peak_group_rss_bytes=d['peak_group_rss_bytes'],audits=parsed))
assert sum(x['audits']['axiom_audits'] for x in results)==11
out=Path(__file__).with_name('parent-probe12-inspection01.json');assert not out.exists();result=dict(status='passed',modules=results,exact_existing_type_axiom_pairs=11,parent_kernel_runs=0,admission='At most eight successor modules under unchanged limits; no scope beyond qualified cut plus accepted joined constructor',full_transfer='OPEN');out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status='passed',modules=2,audits=11,objects=[x['object_bytes'] for x in results],parent_kernel_runs=0)))
