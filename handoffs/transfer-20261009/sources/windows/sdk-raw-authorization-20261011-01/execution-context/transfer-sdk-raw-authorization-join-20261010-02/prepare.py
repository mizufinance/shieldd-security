"""Prepare one bounded admission-reflection proof with complete audited imports."""
import hashlib
import json
from pathlib import Path
import re
import shutil

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PRIOR = DIAG / 'transfer-concrete-cofactor-model-20261010-02'
POOL = DIAG / 'transfer-sdk-raw-authorization-floor-20261010-01'

def pin(path):
    path = Path(path)
    with path.open('rb') as stream:
        sha = hashlib.file_digest(stream, 'sha256').hexdigest()
    return {'path': str(path), 'bytes': path.stat().st_size, 'sha256': sha}

floor = json.loads((POOL / 'composition-review.json').read_text())
assert floor['admission_ready'] and floor['kernel_credit'] == 0 and floor['objects'] == 432
owned = [record['copy'] for record in floor['selected']]
for record in owned:
    assert pin(record['path']) == record
assert {str(p) for p in (POOL / 'modules/ShielddSecurity').iterdir()} == {r['path'] for r in owned}
source = ROOT / 'handwritten/SDKRawAuthorization01.lean'
text = source.read_text()
names = ['ShielddSecurity.SDKRawAuthorization01.' + name
         for name in re.findall(r'^(?:noncomputable )?(?:theorem|lemma|def) ([A-Za-z0-9_]+)', text, re.M)]
assert len(names) == 13
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
plan['targets'] = [{'module': 'SDKRawAuthorization01', 'source': pin(target),
                    'predecessor_source': pin(source), 'imports': ['ShielddSecurity.SDKNativeSpendAuth01', 'ShielddSecurity.ShielddNativeAuthorizationRaw', 'Mathlib.Data.List.OfFn'],
                    'audit_names': names}]
plan['pins'] += [pin(Path(__file__)), pin(ROOT / 'prepare_fresh.py'), pin(ROOT / 'source-review.json'), pin(ROOT / 'prepare_recipe.py'), pin(ROOT / 'prepare_recipe02.py'), pin(ROOT / 'prepare_recipe03.py'), pin(ROOT / 'prepare_recipe04.py'), pin(ROOT / 'predecessor_prepare_stage03.py'), pin(ROOT / 'predecessor_prepare_stage.py'), pin(source), pin(target), pin(runner),
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
plan['pins'] += [pin(ROOT.parent / 'transfer-sdk-raw-authorization-join-20261010-01' / name) for name in ['plan.json','events.jsonl','execute_bounded.py','prepare.py','handwritten/SDKRawAuthorization01.lean','runs/01-SDKRawAuthorization01/stdout.txt']]
plan['kind'] = 'MATHEMATICAL_SDK_CODEC_SUCCESSOR'
plan['scope'] = 'Owned raw Scalar/coordinate reader/private scalar/encoder/Point authorization programs compose with production SDK randomization in the concrete mathematical Jubjub model. Raw generator identifies independently certified actual SDK base without an exact-order premise. Successful input admission yields actual raw authorization output; independent output admission supplies all six native witness arithmetic constraints. A concrete admitted nonidentity key cancels to identity with scalar one, proving the separate output gate necessary. Global Rust/FFI primitive contracts, original circuit rows/copies and full Transfer remain OPEN. Global byte-array encoding meaning derives SDK injectivity/coherence and identifies the admitted actual key subgroup/nonidentity without an abstract subgroup-decoder law. No runtime/BMC/negative-control/certification credit.'
plan['source_repairs'] = 'Fresh additive-group neg_nsmul lemma-name repair. Failed predecessor preserved with zero proof/control/certification credit; finite guards unchanged.'
(ROOT / 'plan.json').write_text(json.dumps(plan, sort_keys=True, separators=(',', ':')) + '\n')
review = {'plan': pin(ROOT / 'plan.json'), 'runner': pin(runner), 'owned_objects': len(owned),
          'owned_import_pool': pin(POOL / 'composition-review.json'), 'audits': len(names), 'scope': plan['scope']}
(ROOT / 'review.json').write_text(json.dumps(review, indent=2) + '\n')
assert sum(p.stat().st_size for p in ROOT.rglob('*') if p.is_file()) + 6*8*1024**2 + 1024**2 + 256*1024 < 128*1024**2
print(json.dumps(review))
