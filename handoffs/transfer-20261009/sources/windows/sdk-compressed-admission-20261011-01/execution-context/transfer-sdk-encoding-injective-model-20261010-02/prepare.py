"""Prepare one bounded admission-reflection proof with complete audited imports."""
import hashlib
import json
from pathlib import Path
import re
import shutil

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-concrete-cofactor-model-20261010-02'
POOL = DIAG / 'transfer-sdk-codec-owned-floor-20261010-01'

def pin(path):
    path = Path(path)
    with path.open('rb') as stream:
        sha = hashlib.file_digest(stream, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}

floor = json.loads((POOL / 'composition-review.json').read_text())
assert floor['admission_ready'] and floor['kernel_credit'] == 0 and floor['objects'] == 411
owned = [record['copy'] for record in floor['selected']]
for record in owned:
    assert pin(record['path']) == record
assert {str(p) for p in (POOL / 'modules/ShielddSecurity').iterdir()} == {r['path'] for r in owned}
source = ROOT / 'handwritten/SDKEncodingInjective01.lean'
text = source.read_text()
names = ['ShielddSecurity.SDKEncodingInjective01.' + name
         for name in re.findall(r'^(?:noncomputable )?(?:theorem|lemma|def) ([A-Za-z0-9_]+)', text, re.M)]
assert len(names) == 10
assert re.findall(r'^#check @([^\n]+)', text, re.M) == names
assert re.findall(r'^#print axioms ([^\n]+)', text, re.M) == names
assert not re.search(r'\b(?:sorry|admit|axiom)\b', re.sub(r'/--[\s\S]*?-/', '', text))
project = ROOT / 'project/ShielddSecurity'
project.mkdir(parents=True, exist_ok=False)
target = project / source.name
shutil.copyfile(source, target)
runner = ROOT / 'execute_bounded.py'
assert pin(PRIOR / 'execute_bounded.py')['sha256'] == '7237060ba9e0d0b98e93cfe5aceb86a4d7390e2af2471b43e39cf3750ebc642b'
shutil.copyfile(PRIOR / 'execute_bounded.py', runner)
plan = json.loads((PRIOR / 'plan.json').read_text())
plan['owned_import_pool'] = pin(POOL / 'composition-review.json')
plan['owned_imports'] = owned
plan['lean_path'] = [str(POOL / 'modules'), str(ROOT / 'project')] + plan['lean_path'][2:]
plan['targets'] = [{'module': 'SDKEncodingInjective01', 'source': pin(target),
                    'predecessor_source': pin(source), 'imports': ['ShielddSecurity.SDKCompressedDecoder01', 'ShielddSecurity.SDKByteIterator01'],
                    'audit_names': names}]
plan['pins'] += [pin(Path(__file__)), pin(ROOT / 'prepare_recipe.py'), pin(source), pin(target), pin(runner),
                 pin(POOL / 'composition-review.json'), pin(POOL / 'prepare.py'), pin(POOL / 'prepare_recipe.py')]
plan['pins'] += floor['input_records'] + owned
plan['pins'] += [pin(DIAG / 'transfer-sdk-source-binding-20261010-01/source-identities.json'),
                 pin(DIAG / 'transfer-sdk-source-binding-20261010-01/sources/jubjub-0.10.0/src/lib.rs'),
                 pin(DIAG / 'transfer-sdk-source-binding-20261010-01/sources/reddsa-0.5.2/src/verification_key.rs')]
unique = {}
for record in plan['pins']:
    assert record['path'] not in unique or unique[record['path']] == record
    unique[record['path']] = record
plan['pins'] = list(unique.values())
plan['kind'] = 'MATHEMATICAL_SDK_CODEC_SUCCESSOR'
plan['scope'] = 'Mathematical compressed encoding is injective over the full concrete curve, including zero-root and torsion points. Exact canonical32-byte integer encoding and y/parity uniqueness derive decoded point identity globally. Ten full audits. Actual native Rust field/to_bytes/array/strict decoder/sqrt representation and full Transfer remain OPEN. No runtime/BMC/control/certification credit.'
plan['source_repairs'] = 'New handwritten input-boundary proof; no generated edits or new axioms.'
(ROOT / 'plan.json').write_text(json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n')
review = {'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'owned_objects': len(owned),
          'owned_import_pool': pin(POOL / 'composition-review.json'), 'audits': len(names), 'scope': plan['scope']}
(ROOT / 'review.json').write_text(json.dumps(review, indent=2) + '\n')
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6*8*1024**2 + 1024**2 + 256*1024 < 128*1024**2
print(json.dumps(review))
