"""Read-only review of retained receipts; no test execution or certification."""
import hashlib, json, re, subprocess
from pathlib import Path

OUT = Path(__file__).resolve().parent
D = OUT.parent / 'transfer-implementation-20261002'
R = Path('C:/src/shieldd-pr160-844389ee')
PIN = '844389ee069e1fb2e576708842d0b389b4d9a44a'
def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda: f.read(1048576), b''): h.update(block)
    return h.hexdigest()
def read(p): return json.loads(p.read_bytes())
def pin(p): return dict(path=str(p), bytes=p.stat().st_size, sha256=sha(p))
def git(*args): return subprocess.check_output(['git', '-C', str(R), *args])
assert git('rev-parse', 'HEAD').decode().strip() == PIN
assert git('status', '--porcelain=v1') == b''
packet = D / 'transfer-coherent-controls-execution-23'
m = read(packet / 'manifest.json')
assert m['pin'] == PIN
source = D / m['source_packet']
assert sha(source / 'manifest.json') == m['source_manifest_sha256']
for name, wanted in read(source / 'packet-inputs.json').items():
    assert sha(source / name) == wanted, name
builds = {}
for job in m['jobs']:
    if job['kind'] in ('build_tests', 'build_examples'):
        p = D / job['output']
        b = read(p / 'build-receipt.json')
        assert b['source_manifest_sha256'] == m['source_manifest_sha256']
        assert b['stage'] == m['source_child']
        builds[job['kind']] = b
records, common_source, common_registry = [], None, None
for job in m['jobs']:
    p = D / job['output']
    assert (p / 'exit.txt').read_text().strip() == '0', job['output']
    assert (p / 'wrapper-exit.txt').read_text().strip() == '0', job['output']
    assert not any((p / n).exists() for n in ['stop.txt', 'wrapper-exception.txt'])
    events = dict(line.split() for line in (p / 'cgroup-memory-events-after.txt').read_text().splitlines())
    assert int(events['oom_kill']) == 0 and int(events['oom']) == 0
    assert not (p / 'cgroup-cgroup-procs-after.txt').read_text().strip()
    assert not (p / 'owned-group-after.txt').read_text().strip()
    checks = []
    for before, after in [('source-inputs.txt','source-inputs-after.txt'),
        ('sdk-source-before.txt','sdk-source-after.txt'), ('app-source-before.txt','app-source-after.txt'),
        ('formal-exporters-before.txt','formal-exporters-after.txt'),
        ('setup-source-before.txt','setup-source-after.txt'),
        ('runner-script-before.txt','runner-script-after.txt'),
        ('memory-helper-before.txt','memory-helper-after.txt')]:
        assert (p / before).read_bytes() == (p / after).read_bytes(), (p, before)
        checks.extend([pin(p / before), pin(p / after)])
    runner_hash, runner_path = (p / 'runner-script-before.txt').read_text().strip().split(maxsplit=1)
    actual_runner = Path(runner_path.replace('/mnt/c/', 'C:/', 1))
    assert sha(actual_runner) == runner_hash
    record = dict(index=job['index'], kind=job['kind'], output=job['output'],
        scope=job['scope'], runner=pin(actual_runner), paired_receipts=checks,
        receipts=[pin(p / n) for n in ['exit.txt','wrapper-exit.txt','stdout.txt','stderr.txt',
            'cgroup-memory-events-after.txt','cgroup-cgroup-procs-after.txt','owned-group-after.txt']])
    if job['kind'] != 'stage':
        assert (p / 'full-source-before.json').read_bytes() == (p / 'full-source-after.json').read_bytes()
        assert (p / 'registry-before.json').read_bytes() == (p / 'registry-after.json').read_bytes()
        current = read(p / 'full-source-before.json')
        registry = read(p / 'registry-before.json')
        if common_source is None: common_source, common_registry = current, registry
        assert current == common_source and registry == common_registry
        record['receipts'].extend(pin(p / n) for n in ['full-source-before.json',
            'full-source-after.json','registry-before.json','registry-after.json'])
    if job['kind'] in ('test','branch','alternate_setup'):
        receipt = read(p / 'runtime-completed.json')
        binary = read(p / 'binary-before.json')
        assert receipt['status'] == 'exact_runtime_job_completed' and receipt['binary'] == binary
        build = builds['build_tests' if job['kind'] == 'test' else 'build_examples']
        assert build['binaries'][job['binary']] == binary
        record['binary'] = binary
        record['receipts'].extend(pin(p / n) for n in ['runtime-completed.json','binary-before.json'])
    if job['kind'] == 'test':
        stdout = (p / 'stdout.txt').read_text()
        names = re.findall(r'^test (\S+) \.\.\. ok$', stdout, re.M)
        assert sorted(names) == sorted(job['names']) and len(names) == len(set(names))
        count = len(names)
        assert len(re.findall(rf'^test result: ok\. {count} passed; 0 failed; 0 ignored;', stdout, re.M)) == 1
        group = read(p / 'group-result.json')
        assert sorted(group['names']) == sorted(names) and group['tests'] == count
        assert group['libtest_log_sha256'] == sha(p / 'libtest-results.txt')
        record.update(names=names, tests=count, result='RETAINED_EXACT_NAMED_TEST_PASS')
        record['receipts'].extend(pin(p / n) for n in ['group-result.json','libtest-results.txt'])
    elif job['kind'] == 'branch':
        lines = [line[len('BRANCH_GENUINE_PASS '):] for line in (p / 'stdout.txt').read_text().splitlines()
                 if line.startswith('BRANCH_GENUINE_PASS ')]
        assert len(lines) == 1
        facts = json.loads(lines[0])
        assert facts['case'] == job['name'] and facts['statement_fields'] == 64
        record.update(observation=facts, result='RETAINED_GENUINE_BRANCH_PASS')
    records.append(record)
base = {name.decode(): sha(R / name.decode()) for name in git('ls-files','-z').split(b'\0') if name}
changed = {name: dict(clean_checkout_sha256=base.get(name), retained_source_sha256=value)
           for name,value in common_source.items() if base.get(name) != value}
missing = sorted(set(base) - set(common_source))
assert git('status','--porcelain=v1') == b'' and git('rev-parse','HEAD').decode().strip() == PIN
report = dict(kind='READ_ONLY_RETAINED_RUNTIME_RECEIPT_REVIEW', runtime_sha=PIN,
    manifest=pin(packet / 'manifest.json'), source_manifest=pin(source / 'manifest.json'),
    source_inventory_files=len(common_source), exact_named_tests=sum(r.get('tests',0) for r in records),
    genuine_branches=sum(r['kind']=='branch' for r in records), jobs=records,
    registry_files=common_registry, raw_checkout_differences=changed, missing_clean_tracked_files=missing,
    scope='Retained exact successful executions and their captured source/binary/registry/guard associations; no new replay. Raw identity comparison is not semantic correspondence.',
    boundaries=['Native testing is distinct from a Lean proof or bounded model checking.',
        'The source is an explicitly overlaid diagnostic descendant of the clean full SHA; runtime and dependency differences require semantic review.',
        'Host queue tests inject canonical no-action entries directly, not genuine admitted Transfer transactions. Same-instance retry drains the failed queue and can commit an empty diagnostic block.',
        'Six permanent-store tests cover their finite fixtures and recovery boundaries, not every IO-failure interleaving or post-commit completion error.',
        'Live source/binary/registry rehash and complete overlay semantic correspondence have not been performed by this review.',
        'Full original-row G3/G4 composition and full Transfer certification remain OPEN.'],
    new_runtime_executions=0, proof_credit=0, certification=False)
target = OUT / 'review.json'
assert not target.exists()
target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(report=pin(target), tests=report['exact_named_tests'],branches=report['genuine_branches'],
    changed_paths=list(changed),missing_clean_tracked_files=missing)))
