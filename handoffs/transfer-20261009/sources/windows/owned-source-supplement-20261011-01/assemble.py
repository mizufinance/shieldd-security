import base64
import hashlib
import io
import json
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent
COMPOSITION = ROOT.parent / 'transfer-envelope-owned-floor-20261010-01/composition-review.json'
COMPOSITION_SHA = 'ab4f8c06742e6696255e8401e59abcf01ecbdd2d2c73732b95f290b9a7c280f3'
NAMES = 'Arithmetic Compiler EdwardsWeierstrassAlgebra01 EdwardsWeierstrassEquiv01 EdwardsWeierstrassExceptions01 EdwardsWeierstrassMap01 Group GroupByteCodec GroupExtended GroupFixedWindows GroupNativeMultiply GroupScalarCodec GroupWindows Jubjub Rows Scalar ScalarBits ScalarComparisonBounds ScalarRows TransferOwnership TransferReduction TransferWindows'.split()

def digest(data):
    return hashlib.sha256(data).hexdigest()

def pin(path):
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': digest(data)}

archive = ROOT / 'portable-g7-owned-source-supplement01.tar.xz'
manifest_path = ROOT / 'manifest.json'
if archive.exists() or manifest_path.exists():
    raise SystemExit('Fresh sealed packet required')
composition_bytes = COMPOSITION.read_bytes()
assert len(composition_bytes) == 851830 and digest(composition_bytes) == COMPOSITION_SHA
composition = json.loads(composition_bytes)
selected = {entry['module']: entry for entry in composition['selected']}
assert len(selected) == 437 and len(NAMES) == len(set(NAMES)) == 22
payload = []
records = []
for name in NAMES:
    entry = selected[name]
    original = entry['source']
    data = Path(original['path']).read_bytes()
    assert len(data) == original['bytes'] and digest(data) == original['sha256'], name
    relative = 'source/ShielddSecurity/' + name + '.lean'
    destination = ROOT / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    assert not destination.exists()
    destination.write_bytes(data)
    assert destination.read_bytes() == data
    payload.append((relative, data))
    records.append({'module': name, 'archive_path': relative,
                    'bytes': len(data), 'sha256': digest(data),
                    'original_selected_record': entry})
recipe = Path(__file__)
manifest = {
    'schema': 'transfer-g7-exact-owned-source-supplement-v1',
    'status': 'source_only_sealed_transport',
    'scope': 'Exactly the 22 requested original selected Lean source byte streams. No normalization, replay, qualification, merged-source selection, or certification.',
    'composition_manifest': pin(COMPOSITION),
    'composition_selected_count': 437,
    'recipe': pin(recipe),
    'source_count': len(records),
    'sources': records,
    'new_proof_credit': 0, 'new_runtime_credit': 0, 'certification': False,
}
manifest_data = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
manifest_path.write_bytes(manifest_data)
payload.extend([('manifest.json', manifest_data), ('assemble.py', recipe.read_bytes())])
with tarfile.open(archive, 'w:xz', preset=6) as tar:
    for relative, data in sorted(payload):
        info = tarfile.TarInfo(relative)
        info.size = len(data)
        info.mode = 0o644
        info.mtime = 0
        tar.addfile(info, io.BytesIO(data))
with tarfile.open(archive, 'r:xz') as tar:
    assert len(tar.getmembers()) == 24
    for relative, data in payload:
        assert tar.extractfile(relative).read() == data
for record in records:
    assert pin(Path(record['original_selected_record']['source']['path'])) == record['original_selected_record']['source']
assert pin(COMPOSITION)['sha256'] == COMPOSITION_SHA
print(json.dumps({'archive': pin(archive), 'manifest': pin(manifest_path),
                  'sources': len(records), 'source_bytes': sum(e['bytes'] for e in records),
                  'archive_members': 24,
                  'transport_parts': (len(base64.b64encode(archive.read_bytes())) + 11999) // 12000,
                  'new_proof_credit': 0, 'new_runtime_credit': 0}, indent=2))
