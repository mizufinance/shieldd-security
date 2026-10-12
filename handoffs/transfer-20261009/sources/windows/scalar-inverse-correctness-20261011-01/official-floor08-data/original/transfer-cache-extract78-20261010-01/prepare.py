"""Prepare two disjoint finite isolated extractions from existing cache archives."""
import hashlib
import json
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
LOOKUP = DIAG / 'transfer-cache-lookup-20261010-01'
def pin(p):
    p = Path(p)
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
lookup = json.loads((LOOKUP / 'plan.json').read_text())
result = json.loads((LOOKUP / 'result.json').read_text())
assert result['status'] == 'passed'
assert result['stdout_sha256'] == pin(LOOKUP / 'stdout.txt')['sha256']
pairs = dict(re.findall(r'^([A-Za-z0-9_.]+): (.+\.ltar)$', (LOOKUP / 'stdout.txt').read_text(), re.M))
assert set(pairs) == set(lookup['modules']) and len(pairs) == 78
old = json.loads((DIAG / 'transfer-external-floor-complete-20261010-01/external-floor.json').read_text())
for batch in [1, 2]:
    dest = DIAG / ('transfer-cache-extract78-20261010-%02d' % (batch + 1))
    dest.mkdir(exist_ok=False)
    extracted = dest / 'extracted'
    extracted.mkdir()
    modules = lookup['modules'][(batch - 1) * 39:batch * 39]
    runner_text = (LOOKUP / 'execute_metadata.py').read_text()
    runner_text = runner_text.replace("assert plan['command'][1] == 'lookup' and plan['command'][2:] == plan['modules']\nassert len(plan['modules']) == 78",
        "assert len(plan['modules']) == 39\nassert plan['command'][1:5] == ['--jobs', '1', '-x', '-C']\nassert plan['command'][5] == str(ROOT / 'extracted')\nassert plan['command'][6:] == [p['path'] for p in plan['archives']]\nassert Path(plan['command'][0]).name == 'leantar.exe'")
    assert "== 'lookup'" not in runner_text
    (dest / 'execute_metadata.py').write_text(runner_text, encoding='utf-8', newline='\n')
    archives = [pin(pairs[m]) for m in modules]
    pins = [pin(Path(__file__)), pin(dest / 'execute_metadata.py'), pin(LOOKUP / 'plan.json'),
        pin(LOOKUP / 'result.json'), pin(LOOKUP / 'stdout.txt'),
        pin(DIAG / 'transfer-prerequisite-floor-20261010-06/execute_bounded.py')]
    pins += archives + [p for m in modules for p in [old['modules'][m]['source']] + old['modules'][m]['objects']]
    exe = Path(lookup['toolchain_bin']) / 'leantar.exe'
    pins += [pin(exe)]
    plan = {**lookup, 'kind': 'ISOLATED_EXISTING_OFFICIAL_CACHE_EXTRACTION', 'pins': pins,
        'modules': modules, 'archives': archives, 'cwd': str(dest),
        'command': [str(exe), '--jobs', '1', '-x', '-C', str(extracted)] + [p['path'] for p in archives],
        'scope': 'Thirty-nine named cached archive identities from official cache hashing lookup; single-thread extraction only inside a fresh scratch root. No downloads, canonical object overwrites, builds, native replay or theorem/control credit. All created files counted, old sources/objects/archive inputs pinned before and after.'}
    (dest / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'batch': batch, 'plan': pin(dest / 'plan.json'), 'archive_bytes_read_only': sum(p['bytes'] for p in archives)}))
