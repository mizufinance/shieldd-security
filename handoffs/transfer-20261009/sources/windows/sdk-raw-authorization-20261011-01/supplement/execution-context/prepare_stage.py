"""Audit the omitted public definition in the exact retained SDK object."""
import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
def pin(path):
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
floor = json.loads((DIAG/'transfer-sdk-raw-authorization-floor-20261010-01/composition-review.json').read_text())
retained = next(r for r in floor['selected'] if r['module']=='GroupNativeSdk')
assert retained['source']['sha256']=='98972ed777924e873789eb844d88632659b9887445a719b9e165b3c8a85fb2ad'
assert retained['object']['sha256']=='22d379e2469dc0b05df43061d14d5d0a8fe0b6e755fa3c25e31812f81194eb7e'
for key in ['source','object','copy']:
    assert pin(Path(retained[key]['path']))==retained[key]
(ROOT/'retained-sdk-association.json').write_text(json.dumps({'retained':retained,
    'sealed_archive':pin(DIAG/'transfer-sdk-raw-authorization-endpoint-20261010-01/portable-windows-sdk-raw-authorization-endpoint01.tar.xz'),
    'scope':'One missing full declaration type/axiom report against the unchanged qualified SDK source/object. Sealed172-report packet preserved.'},indent=2)+'\n')
recipe=(DIAG/'transfer-sdk-raw-authorization-join-20261010-01/prepare.py').read_text()
recipe=recipe.replace('SDKRawAuthorization01','SDKCoordinateBytesAudit01')
start=recipe.index('names = [');end=recipe.index('assert re.findall',start)
recipe=recipe[:start]+"names = ['ShielddSecurity.GroupNativeSdk.coordinateBytes']\n"+recipe[end:]
recipe=recipe.replace("['ShielddSecurity.SDKNativeSpendAuth01', 'ShielddSecurity.ShielddNativeAuthorizationRaw', 'Mathlib.Data.List.OfFn']", "['ShielddSecurity.GroupNativeSdk']")
start=recipe.index("plan['pins'] += [pin(Path(__file__))");end=recipe.index("plan['pins'] += floor",start)
recipe=recipe[:start]+"plan['pins'] += [pin(Path(__file__)), pin(ROOT / 'prepare_stage.py'), pin(ROOT / 'retained-sdk-association.json'), pin(source), pin(target), pin(runner), pin(POOL / 'composition-review.json'), pin(POOL / 'prepare.py'), pin(POOL / 'prepare_recipe.py')]\n"+recipe[end:]
start=recipe.index("plan['scope'] = ");end=recipe.index("plan['source_repairs']",start)
recipe=recipe[:start]+"plan['scope'] = 'One supplemental full type/axiom report for public GroupNativeSdk.coordinateBytes against exact retained source98972ed/object22d379e. No SDK source/object change and no reseal/replay of172-report packet; Rust primitive correspondence and full Transfer remain OPEN.'\n"+recipe[end:]
recipe=recipe.replace('New handwritten input-boundary proof; no generated edits or new axioms.','Audit-only importer; no proof/source repair, new axioms or physical guard changes.')
recipe=recipe.replace('MATHEMATICAL_SDK_CODEC_SUCCESSOR','RETAINED_SDK_COORDINATE_BYTES_DIAGNOSTIC')
recipe=recipe.replace("plan['kind'] =", "plan['pins'] += [pin(ROOT.parent / 'transfer-sdk-program-prerequisites-20261010-01' / name) for name in ['plan.json','events.jsonl','source-review.json','handwritten/GroupNativeSdk.lean']]\nplan['kind'] =")
ast.parse(recipe)
(ROOT/'prepare.py').write_text(recipe,encoding='utf-8',newline='\n')
print(json.dumps({'retained_source':retained['source'],'retained_object':retained['object'],'audits':1,'guard_changes':False}))
