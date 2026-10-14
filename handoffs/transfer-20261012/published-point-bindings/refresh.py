"""Reproduce sources and atomically qualify the corrected publication constructor."""
from pathlib import Path
import argparse, hashlib, json, os, re, subprocess, sys

root = Path(__file__).resolve().parent
ap = argparse.ArgumentParser()
ap.add_argument('--batch', type=Path, required=True)
ap.add_argument('--output', type=Path, required=True)
a = ap.parse_args()
assert not a.output.exists()
pending = a.output.with_name(a.output.name + '.pending')
assert not pending.exists()
pending.mkdir()
config = json.loads((root / 'config.json').read_text())
verified = {}

def pin(path):
    path = Path(path)
    return dict(path=str(path), bytes=path.stat().st_size,
                sha256=hashlib.sha256(path.read_bytes()).hexdigest())

def checked(identity):
    path = Path(identity['path'])
    stamp = (path.stat().st_size, path.stat().st_mtime_ns)
    if verified.get(str(path)) == (stamp, identity):
        return
    assert pin(path) == identity, str(path)
    verified[str(path)] = (stamp, identity)

completion = json.loads((a.batch / 'completion.json').read_text())
assert completion['status'] == 'passed' and completion['root'] == config['root']
checked(completion['dependency_manifest'])
plan = json.loads(Path(completion['dependency_manifest']['path']).read_text())
assert plan['runtime_sha'] == config['runtime_sha'] and plan['mathlib'] == config['mathlib']
assert plan['limits'] == dict(threads=1, default_heap_MiB=2048,
    elliptic_point_closure_heap_MiB=3072, rss_bytes=4*1024**3,
    module_seconds=240, heartbeats=900000, recDepth=8192,
    free_memory_percent=15, free_disk_bytes=2*1024**3)
assert any(v['sha256'] == config['guard_sha256'] for v in completion['final_files'].values())
for identity in completion['final_files'].values():
    checked(identity)
checked(plan['source_replacements'])
assert plan['source_replacements']['sha256'] == config['source_replacements_sha256']
replacements = json.loads(Path(plan['source_replacements']['path']).read_text())
for name, change in replacements['replacements'].items():
    assert plan['selected'][name]['source'] == change['replacement']

# Check the recursive signatures independently of the runner's reuse decisions.
signatures = {}
def signature(name):
    if name in signatures:
        return signatures[name]
    row = plan['selected'][name]
    children = [(n, signature(n.removeprefix('ShielddSecurity.'))
        if n.startswith('ShielddSecurity.') else None) for n in row['imports']]
    result = hashlib.sha256(json.dumps([row['source']['sha256'], children],
        separators=(',', ':')).encode()).hexdigest()
    assert result == row['source_signature'], name
    if row['replacement_affected'] and not row['replay']:
        assert row['previous_source_signature'] == result, name
    signatures[name] = result
    return result
for name in plan['selected']:
    signature(name)

sources = {p.stem: p for p in (root/'source/ShielddSecurity').glob('*.lean')}
generation = {}
for folder, settings in config['generators'].items():
    dest = pending / folder
    command = [sys.executable, '-B', '-I', '-S', str(root/folder/'generate.py')]
    command += ['--output', str(dest)] if settings['named_output'] else [str(dest)]
    subprocess.run(command, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    for source in (dest/'source-root/ShielddSecurity').glob('*.lean'):
        assert source.stem not in sources
        sources[source.stem] = source
        generation[source.stem] = {k:v for k,v in pin(source).items() if k != 'path'}

fresh = {row['module']: row['receipt'] for row in completion['completed']}
assert list(fresh) == plan['order']
modules, reports = {}, []
for name, source in sorted(sources.items()):
    selected = plan['selected'][name]
    identity = fresh[name] if selected['replay'] else selected['receipt']
    checked(identity)
    receipt = json.loads(Path(identity['path']).read_text())
    assert receipt['module'] == name and receipt['status'] == 'passed'
    assert receipt['exit'] == 0 and receipt['stop'] is None and receipt['audit_error'] is None
    assert receipt['source'] == selected['source']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == receipt['source']['sha256']
    for key in ['source', 'stdout', 'stderr', 'dependency_manifest']:
        checked(receipt[key])
    assert not Path(receipt['stderr']['path']).read_bytes().strip()
    if not selected['replay']:
        assert selected['object'] == receipt['objects']['.olean']
    for value in receipt['objects'].values():
        checked(value)
    names = re.findall(r'(?m)^#check @([A-Za-z0-9_.]+)\s*$', source.read_text())
    assert names and [r['name'] for r in receipt['audits']] == names
    for report in receipt['audits']:
        assert set(report['axioms']) <= {'propext', 'Quot.sound', 'Classical.choice'}
        assert hashlib.sha256(report['full_type'].encode()).hexdigest() == report['full_type_sha256']
    assert receipt['seconds'] <= 240 and receipt['peak_group_rss_bytes'] <= 4*1024**3
    assert all(s['free_memory_percent'] >= 15 and s['free_disk_bytes'] >= 2*1024**3
               for s in receipt['samples'])
    modules[name] = dict(source_sha256=receipt['source']['sha256'],
        source_signature=signatures[name], receipt_sha256=identity['sha256'],
        object_sha256=receipt['objects']['.olean']['sha256'], reports=len(names),
        seconds=receipt['seconds'], peak_group_rss_bytes=receipt['peak_group_rss_bytes'])
    reports += receipt['audits']

assert 'ShielddSecurity.PublishedInverseConstruction593.legal_completed' in [r['name'] for r in reports]
coverage = json.loads((root/'coverage-base.json').read_text())
prior = set(coverage['known_positions'])
assert coverage['runtime_sha'] == config['runtime_sha'] and len(prior) == 16443
point_entries = json.loads((root/'rows-generator/entries.json').read_text())
inverse_entries = json.loads((root/'inverse-generator/entries.json').read_text())
point_positions = {start+i for start in [5292,6695,8826,10366,11906,13928,15194,16460] for i in range(2)}
inverse_positions = {5294,6697,8828,10368,11908,13930,15196,16462}
assert {e['position'] for e in point_entries} == {p for p in point_positions if p-1 not in point_positions}
assert {e['position'] for e in inverse_entries} == inverse_positions
positions = point_positions | inverse_positions
assert len(positions) == 24 and not prior & positions
evidence = dict(status='passed', runtime_sha=config['runtime_sha'], mathlib=config['mathlib'],
    scope='Eight fixed-base output point equalities and eight nonzero checks on one retained legal-input assignment with corrected scalar mappings. Subgroup proof uses an explicit cofactor preimage for the captured generator; SDK generator identity is not established.',
    modules=modules, reports=len(reports), full_types_and_axioms=reports, generation=generation,
    guard_sha256=config['guard_sha256'], refresh_sha256=pin(Path(__file__))['sha256'],
    dependency_manifest_sha256=completion['dependency_manifest']['sha256'],
    conditional_assertion_coverage=dict(previous_union=len(prior), positions=sorted(positions),
        new_positions=sorted(positions), union=len(prior|positions), remaining=22816-len(prior|positions), total=22816),
    certification=False, native_credit=0, full_transfer='OPEN', circuit_soundness='OPEN',
    total_legal_input_construction='OPEN', computed_public64_binding='OPEN', native_consequence='OPEN')
(pending/'evidence.json').write_text(json.dumps(evidence, indent=2, sort_keys=True)+'\n')
os.replace(pending, a.output)
print(json.dumps(dict(status='passed', modules=len(modules), reports=len(reports))))
