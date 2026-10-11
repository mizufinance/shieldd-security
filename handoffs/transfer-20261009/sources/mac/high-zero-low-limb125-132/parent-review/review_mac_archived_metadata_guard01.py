"""Independent source/identity review; no verifier launch or evidence mutation."""
from pathlib import Path
import ast, hashlib, json, lzma

W = Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work')
J = W / 'resumed-orchestration-20261009-01'
old = W / 'mac-full-arithmetic45-execution125/maintained/guard.py'
new = W / 'mac-full-arithmetic45-execution154/maintained/guard.py'
digest = lambda b: hashlib.sha256(b).hexdigest()
assert digest(old.read_bytes()) == '92c62c3c35fb636851a85ef3ddeaaa9185df6f40ffe2ef26a8ad3b3397634076'
assert digest(new.read_bytes()) == 'd28ca27c67c26fc6bb8b71c83a98e78120a38895b6ede20cbb98d42860b4fa57'
a, b = ast.parse(old.read_bytes()), ast.parse(new.read_bytes())
functions = lambda tree: {n.name: ast.dump(n, include_attributes=False) for n in tree.body if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef))}
fa, fb = functions(a), functions(b)
changed = {n for n in fa if fa[n] != fb.get(n)}
added = set(fb) - set(fa)
assert changed == {'read_pin', 'checked_pin', 'carried_check'}, changed
assert added == {'preserved_configs'}, added
assert set(fa) <= set(fb)
# The complete reviewed textual delta also contains only lzma import, fixed
# storage-map constants and these functions; all launch/monitor/cleanup code
# and physical thresholds remain byte/AST equivalent.
mp = W / 'mac-history-metadata-preservation126-10/archive-map01.json'
raw = mp.read_bytes()
assert len(raw) == 81291 and digest(raw) == 'be421e51900b8e74983322a1602704b0a0a12e33e65dc4fe43d56e47fa71fbd8'
m = json.loads(raw)
assert m['schema'] == 'exact-inactive-configuration-storage01'
records = []
total = 0
for key, r in m['records'].items():
    p, q = Path(key), Path(r['archive']['path'])
    assert p.parent.parent == W and p.name == 'config01.json'
    assert p.parent.name.startswith('mac-full-arithmetic45-execution')
    assert p.parent.name.removeprefix('mac-full-arithmetic45-execution').isdigit()
    assert r['original']['path'] == key and 0 < r['original']['bytes'] <= 16 * 1024 * 1024
    assert q.parent in {mp.parent, W / 'mac-history-metadata-preservation126-09'} and q.suffix == '.xz'
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
c = json.loads((new.parent.parent / 'config01.json').read_bytes())
assert all(c['limits'][k] == v for k, v in physical.items())
assert c['lean_environment']['LEAN_NUM_THREADS'] == '1'
report = {'status': 'PASSED', 'scope': 'Source guard delta and exact historical configuration storage; no new Lean replay',
          'guard': {'path': str(new), 'bytes': new.stat().st_size, 'sha256': digest(new.read_bytes())},
          'baseline_sha256': digest(old.read_bytes()), 'changed_functions': sorted(changed),
          'added_functions': sorted(added), 'physical_limits': physical,
          'storage_map': {'path': str(mp), 'bytes': len(raw), 'sha256': digest(raw)},
          'original_configuration_bytes_verified': total, 'records': records,
          'review': 'Fallback applies only to precisely pinned inactive config paths. Archive and decompressed original identities are both checked, with exact EOF/size/no-trailing checks. Protected history includes the exact archived config keys. Missing arbitrary proof sources or objects still fail closed. Launch, monitoring, exclusive serial lock, limits, and cleanup are unchanged.',
          'full_transfer': 'OPEN'}
out = J / 'mac-archived-metadata-guard-review01.json'
with out.open('x') as f:
    json.dump(report, f, indent=2)
    f.write('\n')
print(json.dumps({'status': report['status'], 'records': len(records), 'original_bytes': total, 'guard_sha256': report['guard']['sha256']}))
