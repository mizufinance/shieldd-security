"""Independent retained-receipt, source-diff and packet review; no builds."""
import hashlib,json,re,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
P=ROOT/'packet01'
R=ROOT.parent.parent/'runtime-snapshot'
def digest(b):return hashlib.sha256(b).hexdigest()
def read(p):return json.loads(p.read_bytes())
m=read(P/'manifest.json')
assert m['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
assert subprocess.check_output(['git','-C',str(R),'rev-parse','HEAD']).decode().strip()==m['runtime_sha']
assert subprocess.check_output(['git','-C',str(R),'status','--porcelain=v1'])==b''
files=m['files']; assert len(files)==1133
by_original={}
for name,pin in files.items():
 path=P/name; b=path.read_bytes()
 assert len(b)==pin['bytes'] and digest(b)==pin['sha256'],name
 assert pin['path'] not in by_original or by_original[pin['path']]==name
 by_original[pin['path']]=name
actual={p.relative_to(P).as_posix() for p in P.rglob('*') if p.is_file()}
assert actual==set(files)|{'manifest.json'}
r=read(P/'receipt-review/review.json'); capture=read(P/'overlay-review/capture.json')
source=None; registry=None; tests=[]; branches=[]; builds={}
for j in r['jobs']:
 q=P/'retained-receipts'/j['output']
 assert (q/'exit.txt').read_text().strip()=='0'
 assert (q/'wrapper-exit.txt').read_text().strip()=='0'
 assert not (q/'owned-group-after.txt').read_text().strip()
 assert not (q/'cgroup-cgroup-procs-after.txt').read_text().strip()
 events=dict(line.split() for line in (q/'cgroup-memory-events-after.txt').read_text().splitlines())
 assert int(events['oom'])==0 and int(events['oom_kill'])==0
 for rec in j['receipts']+j['paired_receipts']:
  assert rec['path'] in by_original
  got=files[by_original[rec['path']]]
  assert got==rec
 pairs=j['paired_receipts'];assert len(pairs)%2==0
 for a,b in zip(pairs[::2],pairs[1::2]):
  assert (P/by_original[a['path']]).read_bytes()==(P/by_original[b['path']]).read_bytes()
 runner=files[by_original[j['runner']['path']]];assert runner==j['runner']
 txt=(q/'runner-script-before.txt').read_text().strip()
 assert txt.split(maxsplit=1)[0]==runner['sha256']
 if j['kind']!='stage':
  cs=read(q/'full-source-before.json'); cr=read(q/'registry-before.json')
  assert (q/'full-source-before.json').read_bytes()==(q/'full-source-after.json').read_bytes()
  assert (q/'registry-before.json').read_bytes()==(q/'registry-after.json').read_bytes()
  if source is None:source,registry=cs,cr
  assert cs==source and cr==registry
 if j['kind'] in ('build_tests','build_examples'):
  builds[j['kind']]=read(q/'build-receipt.json')
 if j['kind'] in ('test','branch','alternate_setup'):
  binary=read(q/'binary-before.json'); done=read(q/'runtime-completed.json')
  assert done['status']=='exact_runtime_job_completed' and done['binary']==binary
  br=builds['build_tests' if j['kind']=='test' else 'build_examples']
  assert br['binaries'][next(n for n,x in br['binaries'].items() if x==binary)]==binary
  assert br['source_manifest_sha256']==r['source_manifest']['sha256']
 if j['kind']=='test':
  stdout=(q/'stdout.txt').read_text()
  names=re.findall(r'^test (\S+) \.\.\. ok$',stdout,re.M)
  assert sorted(names)==sorted(j['names']) and len(names)==len(set(names))
  count=len(names)
  assert len(re.findall(rf'^test result: ok\. {count} passed; 0 failed; 0 ignored;',stdout,re.M))==1
  group=read(q/'group-result.json')
  assert sorted(group['names'])==sorted(names) and group['tests']==count
  assert group['libtest_log_sha256']==digest((q/'libtest-results.txt').read_bytes())
  tests.extend(names)
 if j['kind']=='branch':
  lines=[l[len('BRANCH_GENUINE_PASS '):] for l in (q/'stdout.txt').read_text().splitlines() if l.startswith('BRANCH_GENUINE_PASS ')]
  assert len(lines)==1
  facts=json.loads(lines[0]);assert facts==j['observation'] and facts['statement_fields']==64
  branches.append(facts)
assert len(tests)==23 and len(set(tests))==23 and len(branches)==17
assert len(source)==1239 and registry==r['registry_files']
base={n.decode():digest((R/n.decode()).read_bytes()) for n in subprocess.check_output(['git','-C',str(R),'ls-files','-z']).split(b'\0') if n}
changes={n:dict(clean_checkout_sha256=base.get(n),retained_source_sha256=h) for n,h in source.items() if base.get(n)!=h}
assert changes==r['raw_checkout_differences'] and len(changes)==52
assert not set(base)-set(source)
assert len(capture['differences'])==52 and all(b['current_matches_receipt'] and b['current_sha256']==b['sha256'] for b in capture['binaries'].values())
assert len(capture['binaries'])==6
for diff in capture['differences']:
 c=changes[diff['path']]; assert diff['base_sha256']==c['clean_checkout_sha256'] and diff['overlay_sha256']==c['retained_source_sha256']
 blob=(P/'overlay-review/diffs'/Path(diff['path']+'.diff')).read_bytes()
 assert len(blob)==diff['diff_bytes'] and digest(blob)==diff['diff_sha256']
report=dict(kind='PARENT_INDEPENDENT_RETAINED_RUNTIME_REVIEW',runtime_sha=m['runtime_sha'],
 manifest_sha256=digest((P/'manifest.json').read_bytes()),verified_packet_pins=len(files),
 retained_jobs=len(r['jobs']),exact_named_tests=tests,genuine_branches=branches,source_files=len(source),
 exact_overlay_paths=list(changes),binary_receipt_bindings=6,
 scope='Retained execution receipts and captured identities checked independently; no local build, rerun, live remote artifact rehash or universal refinement.',
 certification=False)
(ROOT/'independent-receipt-review01.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:len(v) if isinstance(v,list) else v for k,v in report.items() if k not in ['genuine_branches','scope','exact_overlay_paths']}))

