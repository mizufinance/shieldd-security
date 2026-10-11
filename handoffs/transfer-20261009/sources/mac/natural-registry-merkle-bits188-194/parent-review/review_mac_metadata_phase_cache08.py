"""Independent exact guard/storage delta review; no verifier or worker mutation."""
from pathlib import Path
import ast, difflib, hashlib, json, lzma, pathlib, tempfile

J = Path(__file__).parent
W = J.parent
def sha(data): return hashlib.sha256(data).hexdigest()
def pin(path):
    data = path.read_bytes()
    return dict(path=str(path), bytes=len(data), sha256=sha(data))
oldmap = W/'mac-history-metadata-preservation126-18/archive-map01.json'
newmap = W/'mac-history-metadata-preservation126-19/archive-map01.json'
assert pin(oldmap)['sha256'] == 'c1c1d059e8e39ae1874556b33606715bbbee2251f5871407986321b066e8a935'
assert pin(newmap) == dict(path=str(newmap), bytes=117560, sha256='82690ba5a3478f336554e7f519c494ed576a77f55bfc1b295bed78d14dcd073b')
a, b = json.loads(oldmap.read_bytes()), json.loads(newmap.read_bytes())
assert a['schema'] == b['schema'] == 'exact-inactive-configuration-storage01'
assert all(b['records'][key] == value for key, value in a['records'].items())
added = {k:v for k,v in b['records'].items() if k not in a['records']}
assert len(added) == 3
for key, value in added.items():
    original, archive = value['original'], value['archive']
    assert original['path'] == key and 0 < original['bytes'] <= 16*1024*1024
    path = Path(archive['path'])
    assert path.is_file() and not path.is_symlink() and pin(path) == archive
    decoder = lzma.LZMADecompressor(memlimit=128*1024*1024)
    data = decoder.decompress(path.read_bytes(), max_length=original['bytes']+1)
    assert decoder.eof and not decoder.unused_data
    assert len(data) == original['bytes'] and sha(data) == original['sha256']

base = W/'mac-full-arithmetic45-execution202/maintained/guard.py'
fresh = W/'mac-full-arithmetic45-execution205/maintained/guard.py'
assert pin(base)['sha256'] == '5be5100aa2e08c47fa2992ca8e88456727c76df829a6269cb49c158e25cddaf1'
assert pin(fresh)['sha256'] == '8843eb3854ca31545517a327c39fe7f185f0097b95fe21d3a0fa78351c3b1b30'
for stage in [203,204]:
    assert (W/f'mac-full-arithmetic45-execution{stage}/maintained/guard.py').read_bytes() == base.read_bytes()
before = base.read_text()
expected = before.replace(str(oldmap),str(newmap)).replace("'bytes': 115712", "'bytes': 117560").replace(pin(oldmap)['sha256'], pin(newmap)['sha256'])
old = "    for identity in config['static_records'].values(): read_pin(identity)\n"
new = "    for identity in config['static_records'].values(): checked_pin(identity)\n"
assert expected.count(old) == 1
expected = expected.replace(old,new)
assert expected == fresh.read_text()
assert "    _CHECKED.clear()\n    carried_check(config)\n" in expected
# Extract existing identity-check functions only. No launch, process, or worker code.
tree = ast.parse(expected)
names = {'require','sha','read_pin','checked_pin'}
pure = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name in names]
assert len(pure) == 4
env = dict(pathlib=pathlib, hashlib=hashlib, lzma=lzma, _CHECKED={}, _ARCHIVE_PROOFS=set())
with tempfile.TemporaryDirectory(prefix='metadata-identity-test-',dir=J) as folder:
    root = Path(folder)
    original = root/'historical.json'
    body = b'{"source":"exact"}\n'
    archive = root/'historical.json.xz'
    archive.write_bytes(lzma.compress(body,preset=1))
    identity = dict(path=str(original),bytes=len(body),sha256=sha(body))
    table = {str(original):dict(original=identity,archive=pin(archive))}
    env['preserved_configs'] = lambda: table
    exec(compile(ast.Module(body=pure,type_ignores=[]),str(fresh),'exec'),env)
    raw_read = env['read_pin']
    reads = []
    def counted(p):
        reads.append(p['path'])
        return raw_read(p)
    env['read_pin'] = counted
    env['checked_pin'](identity)
    first = len(reads)
    env['checked_pin'](identity)
    assert len(reads) == first
    env['_CHECKED'].clear()
    env['checked_pin'](identity)
    assert len(reads) > first and reads[-1] == str(archive)
    # Every byte-consuming read still decodes and hashes the exact original.
    assert env['read_pin'](identity) == body
    archive.write_bytes(b'changed compressed bytes')
    env['_CHECKED'].clear()
    try: env['checked_pin'](identity)
    except RuntimeError: pass
    else: raise AssertionError('Changed archived bytes accepted')
    ordinary = root/'ordinary.json'
    ordinary.write_bytes(body)
    ordinary_pin = pin(ordinary)
    env['checked_pin'](ordinary_pin)
    ordinary.write_bytes(b'changed regular bytes')
    env['_CHECKED'].clear()
    try: env['checked_pin'](ordinary_pin)
    except RuntimeError: pass
    else: raise AssertionError('Changed ordinary bytes accepted')

reader_before = (J/'read_preserved_mac_config07.py').read_text()
reader_after = reader_before.replace(str(oldmap),str(newmap)).replace(pin(oldmap)['sha256'],pin(newmap)['sha256']).replace('len(raw) == 115712','len(raw) == 117560')
(J/'read_preserved_mac_config08.py').write_text(reader_after)
physical = dict(threads=1,heap_MiB=2048,group_rss_bytes=4294967296,module_seconds=240,minimum_free_RAM_percent=15,minimum_free_disk_bytes=2147483648,heartbeats=900000,recdepth=8192)
config = json.loads((fresh.parent.parent/'config01.json').read_bytes())
assert all(config['limits'][k] == v for k,v in physical.items())
assert config['lean_environment']['LEAN_NUM_THREADS'] == '1'
(J/'pending-mac-metadata-phase-cache-guard-delta205.diff').write_text(''.join(difflib.unified_diff(before.splitlines(True),expected.splitlines(True),fromfile=str(base),tofile=str(fresh))))
report = dict(status='PASSED',kind='Exact metadata phase-cache and lossless archive-map19 source review; no verifier launch',guard=pin(fresh),prior_203_204_guards_exact=True,map=pin(newmap),previous_records=len(a['records']),records=len(b['records']),added_records=3,added_original_bytes=sum(v['original']['bytes'] for v in added.values()),prior_records_exact=True,all_added_archive_original_size_sha_eof_verified=True,reader_change='Only immutable map path/size/SHA constants; same bounded LZMA128MiB reader',delta='Discarded static-record read results now use existing checked_pin within one fixed_check phase; fresh phase clears cache; byte-consuming reads unchanged',pure_identity_tests='PASSED; changed ordinary/archive bytes rejected after fresh phase; original bytes remain checked on consuming reads',physical_limits=physical,full_transfer='OPEN')
(J/'mac-metadata-phase-cache-guard-review08.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
