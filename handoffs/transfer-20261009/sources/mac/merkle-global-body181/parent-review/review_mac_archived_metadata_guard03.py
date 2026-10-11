"""Independent source/identity review; no verifier launch or evidence mutation."""
from pathlib import Path
import ast, hashlib, json, lzma

W = Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
J = W / 'resumed-orchestration-20261009-01'
old = W / 'mac-full-arithmetic45-execution168/maintained/guard.py'
new = W / 'mac-full-arithmetic45-execution176/maintained/guard.py'
digest = lambda b: hashlib.sha256(b).hexdigest()
assert digest(old.read_bytes()) == '8eb31ea75351ea4bf2562b1a2a583294c69c73b57f0cfc44e14552e50fcb953c'
assert digest(new.read_bytes()) == 'c89c57b55398743a1206490855d7960630636af66a8208533e85f62a6ac8bf47'
a, b = ast.parse(old.read_bytes()), ast.parse(new.read_bytes())
functions = lambda tree: {n.name: ast.dump(n, include_attributes=False) for n in tree.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))}
fa, fb = functions(a), functions(b)
changed = {n for n in fa if fa[n] != fb.get(n)}
added = set(fb) - set(fa)
assert changed == set(), changed
assert added == set(), added
assert set(fa) == set(fb)
remove_storage=lambda t:ast.dump(ast.Module(body=[n for n in t.body if not(isinstance(n,ast.Assign)and any(isinstance(x,ast.Name)and x.id=='_STORAGE_PIN'for x in n.targets))],type_ignores=[]),include_attributes=False)
assert remove_storage(a)==remove_storage(b)
# The complete reviewed textual delta also contains only lzma import, fixed
# storage-map constants and these functions; all launch/monitor/cleanup code
# and physical thresholds remain byte/AST equivalent.
mp = W / 'mac-history-metadata-preservation126-12/archive-map01.json'
raw = mp.read_bytes()
assert len(raw) == 98535 and digest(raw) == '6c61b1ac941fe7a65e527beaaea17d09906a80cbfe6c00b7d9bb22c382393c45'
m = json.loads(raw)
assert m['schema'] == 'exact-inactive-configuration-storage01'
ancestor=json.loads((W/'mac-history-metadata-preservation126-11/archive-map01.json').read_bytes())
assert all(m['records'][k]==v for k,v in ancestor['records'].items())
records = []
total = 0
for key, r in m['records'].items():
    p, q = Path(key), Path(r['archive']['path'])
    assert p.parent.parent == W and p.name == 'config01.json'
    assert p.parent.name.startswith('mac-full-arithmetic45-execution')
    assert p.parent.name.removeprefix('mac-full-arithmetic45-execution').isdigit()
    assert r['original']['path'] == key and 0 < r['original']['bytes'] <= 16 * 1024 * 1024
    assert q.parent in {mp.parent, W / 'mac-history-metadata-preservation126-10', W / 'mac-history-metadata-preservation126-09',W/'mac-history-metadata-preservation126-11'} and q.suffix == '.xz'
    assert q.is_file() and not q.is_symlink()
    packed = q.read_bytes()
    assert len(packed) == r['archive']['bytes'] and digest(packed) == r['archive']['sha256']
    decoder = lzma.LZMADecompressor(memlimit=128 * 1024 * 1024)
    data = decoder.decompress(packed, max_length=r['original']['bytes'] + 1)
    assert decoder.eof and not decoder.unused_data and len(data) == r['original']['bytes']
    assert digest(data) == r['original']['sha256']
    json.loads(data)
    if p.exists():
        assert not p.is_symlink() and p.read_bytes() == data
    total += len(data)
    records.append({'original': r['original'], 'archive': r['archive']})
physical = {'threads': 1, 'heap_MiB': 2048, 'group_rss_bytes': 4294967296,
            'module_seconds': 240, 'minimum_free_RAM_percent': 15,
            'minimum_free_disk_bytes': 2147483648, 'heartbeats': 900000, 'recdepth': 8192}
import importlib.util
spec=importlib.util.spec_from_file_location('preserved',J/'read_preserved_mac_config03.py');preserved=importlib.util.module_from_spec(spec);spec.loader.exec_module(preserved)
c = json.loads(preserved.read_config(new.parent.parent / 'config01.json'))
assert all(c['limits'][k] == v for k, v in physical.items())
assert c['lean_environment']['LEAN_NUM_THREADS'] == '1'
report = {'status': 'PASSED', 'scope': 'Source guard delta and exact historical configuration storage; no new Lean replay',
          'guard': {'path': str(new), 'bytes': new.stat().st_size, 'sha256': digest(new.read_bytes())},
          'baseline_sha256': digest(old.read_bytes()), 'changed_functions': sorted(changed),
          'added_functions': sorted(added), 'physical_limits': physical,
          'storage_map': {'path': str(mp), 'bytes': len(raw), 'sha256': digest(raw)},
          'original_configuration_bytes_verified': total, 'records': records,
          'review': 'Only immutable storage map constant changed; all guard functions and other code AST identical. Prior151 archive records unchanged; new9 original configurations verified. Fallback applies only to precisely pinned inactive config paths. Archive and decompressed original identities are both checked, with exact EOF/size/no-trailing checks. Protected history includes the exact archived config keys. Missing arbitrary proof sources or objects still fail closed. Launch, monitoring, exclusive serial lock, limits, and cleanup are unchanged.',
          'full_transfer': 'OPEN'}
out = J / 'mac-archived-metadata-guard-review03.json'
with out.open('x') as f:
    json.dump(report, f, indent=2)
    f.write('\n')
print(json.dumps({'status': report['status'], 'records': len(records), 'original_bytes': total, 'guard_sha256': report['guard']['sha256']}))
