"""Compare extracted official cache objects with the existing import pool."""
import hashlib
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
old = json.loads((DIAG / 'transfer-external-floor-complete-20261010-01/external-floor.json').read_text())
lookup_root = DIAG / 'transfer-cache-lookup-20261010-01'
lookup = json.loads((lookup_root / 'plan.json').read_text())
records = []; files = {}; gaps = []; batches = []
for suffix in ['05', '06']:
    batch = DIAG / ('transfer-cache-extract78-20261010-' + suffix)
    result = json.loads((batch / 'result.json').read_text())
    assert result['status'] == 'passed'
    plan = json.loads((batch / 'plan.json').read_text())
    batches.append({'plan': pin(batch / 'plan.json'), 'result': pin(batch / 'result.json')})
    for module, archive in zip(plan['modules'], plan['archives']):
        assert pin(archive['path']) == archive
        entry = old['modules'][module]
        source = entry['source']; assert pin(source['path']) == source
        prefix = module.split('.')[0]
        package = 'mathlib' if prefix == 'Mathlib' else 'batteries'
        relative = module.replace('.', '/')
        base = batch / 'extracted'
        if package != 'mathlib': base = base / '.lake/packages' / package
        objects = []
        for object_record in entry['objects']:
            name = Path(object_record['path']).name
            obj = base / '.lake/build/lib/lean' / Path(relative).parent / name
            extracted = pin(obj)
            current = pin(object_record['path'])
            if (extracted['bytes'], extracted['sha256']) != (current['bytes'], current['sha256']):
                gaps.append({'module': module, 'object': name, 'extracted': extracted, 'current': current})
            objects.append({'existing': current, 'extracted': extracted})
            files[package + '/.lake/build/lib/lean/' + str(Path(relative).parent / name).replace('\\', '/')] = extracted['sha256']
        assert len([p for p in objects if '.olean' in p['existing']['path']]) == 3
        files[package + '/' + relative + '.lean'] = source['sha256']
        records.append({'module': module, 'canonical_source': source, 'archive': archive,
            'objects': objects, 'cache_batch': batch.name})
assert len(records) == 78 and {r['module'] for r in records} == set(lookup['modules'])
assert not gaps, json.dumps(gaps[:2])
summary = {'kind': 'ADDITIONAL_OFFICIAL_CACHE_IDENTITY_SUPPLEMENT', 'admission_ready': True,
    'lookup_plan': pin(lookup_root / 'plan.json'), 'lookup_result': pin(lookup_root / 'result.json'),
    'lookup_output': pin(lookup_root / 'stdout.txt'), 'extraction_batches': batches,
    'records': records, 'files': files, 'mismatches': gaps,
    'scope': 'Required source/olean/private/server and available auxiliary objects for 78 recursive imports. Named archive keys computed by pinned official cache helper from current canonical sources and dependency hashes; existing objects exactly match isolated archives. Embedded build commits may precede current source commit when hashes remain unchanged. This proves object identity to official cache content, not mathematical correspondence or Transfer correctness.',
    'failed_extraction_retained': pin(DIAG / 'transfer-cache-extract78-20261010-02/result.json'),
    'theorem_credit': 0, 'negative_control_credit': 0, 'runtime_credit': 0}
(ROOT / 'qualification.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
print(json.dumps({'qualification': pin(ROOT / 'qualification.json'), 'modules': len(records), 'files': len(files), 'mismatches': 0}))
