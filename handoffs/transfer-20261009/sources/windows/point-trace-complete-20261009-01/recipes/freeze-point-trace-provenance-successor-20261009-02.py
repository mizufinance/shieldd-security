from pathlib import Path
import base64, gzip, hashlib, json

local = Path('C:/src/shieldd-transfer-handoffs')
old = local / 'point-trace-complete-review-packet-20261009-01'
new = local / 'point-trace-complete-review-packet-20261009-02'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text())
assert sha(old / 'manifest.json') == 'b365c3da36b1fd2cec8844e91c5dff486d501a258e3da4b3f10aa2509c2533f0'
assert sha(old.with_suffix('.json.gz')) == '4c4137f0cc9081085c6c807777c219168b96fd5f22300407364f975da2a9ff4b'
assert not new.exists()
new.mkdir()
files = {}
def copy(source, rel):
    target = new / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(source.read_bytes())
    files[rel] = {'sha256': sha(target), 'bytes': target.stat().st_size}
def write(rel, obj):
    target = new / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes((json.dumps(obj, indent=2) + '\n').encode())
    files[rel] = {'sha256': sha(target), 'bytes': target.stat().st_size}
for rel, item in load(old / 'manifest.json')['files'].items():
    assert sha(old / rel) == item['sha256'] and (old / rel).stat().st_size == item['bytes']
    if rel != 'receipt.json':
        copy(old / rel, rel)
supported = local / 'point-trace-isolated-supported-replay-receipt-20261009-01.json'
assert sha(supported) == '3076043add32fef9ce221c45179096239b841cab9f1cf61f6f0cc343f43a99bd'
replay = load(supported)
assert replay['supported_entry_flags'] == ['-I', '-B', '-S'] and replay['modules_byte_exact'] == 249
assert replay['new_kernel_credit'] == replay['new_control_credit'] == 0
assert sha(local / 'replay-point-trace-isolated-20261009-01.py') == replay['recipe_sha256']
copy(supported, 'generation-inputs/isolated-supported-replay-receipt.json')
copy(local / 'replay-point-trace-isolated-20261009-01.py', 'recipes/replay-point-trace-isolated-20261009-01.py')
copy(Path(__file__), 'recipes/' + Path(__file__).name)
receipt = load(old / 'receipt.json')
receipt['supported_portable_replay'] = {'flags': ['-I', '-B', '-S'], 'receipt_sha256': sha(supported),
    'source_input_inventory_sha256': replay['source_input_inventory_sha256'], 'python_version': replay['python_version'],
    'modules_byte_exact': 249, 'new_kernel_credit': 0, 'new_control_credit': 0}
receipt['previous_immutable_packet'] = {'manifest_sha256': sha(old / 'manifest.json'), 'archive_sha256': sha(old.with_suffix('.json.gz')),
    'disposition': 'Retained unchanged; fresh supported replay provenance only, no kernel replay or source change'}
write('receipt.json', receipt)
write('manifest.json', {'kind': 'Fresh immutable complete Point trace/endpoint successor with isolated supported portable replay',
    'files': dict(files), 'review_audit_text_disposition': 'Full successful pp.all type/axiom text retained; no composed caches/toolchains transported', 'full_transfer': 'OPEN'})
archive = new.with_suffix('.json.gz')
assert not archive.exists()
payload = json.dumps({'files': {rel: base64.b64encode((new / rel).read_bytes()).decode() for rel in files}}, separators=(',', ':')).encode()
archive.write_bytes(gzip.compress(payload, mtime=0))
print(json.dumps({'marker': 'TRANSFER_POINT_TRACE_PROVENANCE_SUCCESSOR_PACKET_V1', 'archive': str(archive), 'sha256': sha(archive),
    'manifest_sha256': sha(new / 'manifest.json'), 'bytes': archive.stat().st_size, 'files': len(files),
    'fresh_kernel_modules': 247, 'declaration_audits': 3144, 'qualified_operations': 369,
    'additional_kernel_or_control_credit_from_successor': 0, 'full_transfer': 'OPEN'}))
