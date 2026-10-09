"""Seal import observations only; there is no Point/order certificate proof."""
import hashlib,json,subprocess
from pathlib import Path
from audit_log import validate
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-weierstrass-order07';P=S/'project'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
packet=json.loads((O/'input-packet01.json').read_text())
for key,item in packet['packet']['files'].items():
 assert sha(R/item['source_path'])==item['sha256']==sha(P/'ShielddSecurity'/Path(key).name)
candidate=S/'candidate.json';assert sha(candidate)=='028924209b34a15720e93083253a54b4fe2f759bd19e93e43fdf2707c576096c'
modules=['WeierstrassPointImportFloor07','WeierstrassPointOnlyFloor07','WeierstrassOrderOnlyFloor07','WeierstrassPointDirectAudit07']
observations=[];official=set()
for name in modules:
 receipt=O/f'build-{name}-01.json';r=json.loads(receipt.read_text());source=P/'ShielddSecurity'/(name+'.lean')
 assert r['source_sha256']==sha(source) and sha(receipt.with_suffix('.log'))==r['log_sha256']
 assert '-j1' in r['command'] and '-M2048' in r['command'] and r['lean_heap_limit_MiB']==2048
 assert r['process_group_rss_limit_bytes']==4*1024**3 and r['timeout_seconds']==240
 if name=='WeierstrassOrderOnlyFloor07':
  assert r['status']=='passed' and r['exit']==0
  validate(receipt.with_suffix('.log').read_text(),r['expected_axiom_names'],r['expected_signature_names'])
  assert r['axiom_audits']==1
 else:assert r['status']=='failed' and r['exit']==134 and r.get('axiom_audits') is None
 ext=r['frozen_imports']['official_import_closure'];assert sha(O/ext['manifest_file'])==ext['manifest_sha256'];official.add(O/ext['manifest_file'])
 for name,h in r['guard_sources_sha256'].items():
  current=S/name
  assert sha(current)==h or any(sha(old)==h for old in (O/'source-history').glob(name+'-*'))
 observations.append(dict(module=r['module'],status=r['status'],exit=r['exit'],seconds=r['seconds'],
   peak_group_rss_bytes=r['peak_group_rss_bytes'],audit_count=r.get('axiom_audits'),receipt=str(receipt.relative_to(R)),proof_credit=0))
files={};revisions={}
for path in official:
 d=json.loads(path.read_text())
 for key,h in d['files'].items():
  if key in files:assert files[key]==h
  files[key]=h
 for name,h in d['revisions'].items():
  if name in revisions:assert revisions[name]==h
  revisions[name]=h
for name,h in revisions.items():
 root=P/'.lake/packages'/name
 assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip()==h
 assert not subprocess.check_output(['git','status','--porcelain','--untracked-files=no'],cwd=root,text=True).strip()
for key,h in files.items():
 name,relative=key.split('/',1);root=Path.home()/'.elan/toolchains/leanprover--lean4---v4.30.0' if name=='lean4' else P/'.lake/packages'/name
 assert sha(root/relative)==h
summary=dict(schema='bounded-actual-Point-import-diagnostic-v1',status='resource_refused_Point_import_probe',
 observations=observations,Point_proof_credit=0,OrderOnly_True_marker_credit='import observation only, no point or order theorem',
 root_candidate_kernel_order_proof=False,canonical_owned_closure=67,reused_owned_objects=len(packet['reused']),
 missing_owned_modules_unbuilt=packet['missing_canonical_modules'],official_files_rehashed=len(files),
 source_candidate_sha256=sha(candidate),limits=dict(lean_threads=1,heap_MiB=2048,seconds=240,rss_bytes=4*1024**3),
 interpretation='Point import plus direct actual group-instance audit refuses; no signature output. Phase before versus during command execution is not proven by zero output alone.',
 decision='queue actual Mathlib Point-heavy chain for another host under separately approved bounds; do not replay67 modules on this host or escalate',
 native_generator_identity='OPEN',curve_cardinality='OPEN',full_transfer='OPEN')
(O/'diagnostic-result01.json').write_text(json.dumps(summary,indent=2)+'\n')
inventory=[]
def add(p,category,publish=True):
 inventory.append(dict(path=str(p.relative_to(R)),bytes=p.stat().st_size,sha256=sha(p),category=category,publication=publish))
for p in S.glob('*.py'):add(p,'maintained_guard_or_diagnostic_sealer')
add(candidate,'untrusted_candidate_data')
for name in modules:
 add(P/'ShielddSecurity'/(name+'.lean'),'handwritten_import_diagnostic')
 add(O/f'build-{name}-01.json','pass_or_resource_refusal_receipt')
 add(O/f'build-{name}-01.log','raw_observation_local_only',False)
for p in official:add(p,'deduplicated_official_closure')
for p in O.glob('*.json'):
 if p.name.startswith(('build-','official-imports','publication-')):continue
 add(p,'source_qualification_or_diagnostic_metadata')
for p in O.glob('cache-*.log'):add(p,'raw_cache_observation_local_only',False)
for p in (O/'source-history').glob('*'):add(p,'preserved_guard_predecessor')
for name in ['lakefile.lean','lake-manifest.json','lean-toolchain']:add(P/name,'frozen_package_identity')
assert len(inventory)==len({x['path'] for x in inventory})
manifest=dict(schema='finite-Point-import-diagnostic-publication-v1',files=inventory,proof_credit=0,
 immutable_source_import_identity=True,no_actual_Point_certificate_or_curve_order_claim=True,full_transfer='OPEN')
dest=O/'publication-manifest01.json';assert not dest.exists();tmp=dest.with_suffix('.tmp');tmp.write_text(json.dumps(manifest,indent=2)+'\n');tmp.replace(dest)
print(json.dumps(dict(status='diagnostic_sealed',manifest_sha256=sha(dest),files=len(inventory),publication_files=sum(x['publication'] for x in inventory),Point_proof_credit=0)))
