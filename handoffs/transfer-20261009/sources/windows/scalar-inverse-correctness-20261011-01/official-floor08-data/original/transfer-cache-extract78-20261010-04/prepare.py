"""Fresh successor: tolerate disappearing extraction temporaries while counting stable output."""
import hashlib
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
def pin(p):
    with p.open('rb') as f: sha = hashlib.file_digest(f, 'sha256').hexdigest()
    return {'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha}
for prior_suffix, next_suffix in [('02', '05'), ('03', '06')]:
    prior = DIAG / ('transfer-cache-extract78-20261010-' + prior_suffix)
    dest = DIAG / ('transfer-cache-extract78-20261010-' + next_suffix)
    dest.mkdir(exist_ok=False)
    (dest / 'extracted').mkdir()
    plan = json.loads((prior / 'plan.json').read_text())
    text = (prior / 'execute_metadata.py').read_text()
    marker = 'parser = argparse.ArgumentParser()'
    helper = '''def extraction_usage(stable=False):
    total = metadata = 0
    for path in ROOT.rglob('*'):
        if not path.is_file(): continue
        try: size = path.stat().st_size
        except FileNotFoundError:
            if stable: raise
            continue
        total += size
        if path.suffix in ('.json', '.jsonl', '.txt'): metadata += size
    assert total < 64 * 1024**2 and metadata < 16 * 1024**2, 'Artifact cap'
    return total, metadata
'''
    text = text.replace(marker, helper + '\n' + marker)
    text = text.replace('guards.usage()', 'extraction_usage()')
    text = text.replace("status = {'status': 'passed'", "total, metadata = extraction_usage(stable=True)\n    status = {'all_new_bytes': total, 'metadata_bytes': metadata, 'status': 'passed'")
    (dest / 'execute_metadata.py').write_text(text, encoding='utf-8', newline='\n')
    plan['command'][5] = str(dest / 'extracted')
    plan['cwd'] = str(dest)
    plan['pins'] += [pin(Path(__file__)), pin(prior / 'plan.json'), pin(prior / 'execute_metadata.py'), pin(dest / 'execute_metadata.py')]
    if (prior / 'result.json').is_file(): plan['pins'].append(pin(prior / 'result.json'))
    plan['successor_reason'] = 'Old first extraction stopped on a temporary-file stat race in its byte monitor, zero proof/control credit. Old failed outputs retained. Fresh disjoint successor skips only already-disappeared scratch temporaries during live monitoring and requires stable complete final counts; all limits unchanged. Second unrun sibling preserved and replaced proactively.'
    (dest / 'plan.json').write_text(json.dumps(plan, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'plan': pin(dest / 'plan.json')}))
