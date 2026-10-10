"""Verify all retained original declaration bodies against maintained canonical sources."""
import hashlib
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
PUB = Path('C:/src/shieldd-transfer-windows-publication-20261009/circuits/ShielddSecurity')
def pin(path):
    path = Path(path)
    with path.open('rb') as f: sha=hashlib.file_digest(f,'sha256').hexdigest()
    return {'path':str(path),'bytes':path.stat().st_size,'sha256':sha}
def body(path):
    return '\n'.join(line.rstrip() for line in Path(path).read_text(encoding='utf-8-sig').splitlines()
        if line.strip() and not line.startswith('set_option pp.all true in')
        and not line.startswith('#check ') and not line.startswith('#print axioms '))
original_path=DIAG/'transfer-base-order-import-review-20261010-01/review.json'
original=json.loads(original_path.read_text())
results=[]
for name,r in sorted(original['owned'].items()):
    canonical=PUB/(name.split('.')[-1]+'.lean')
    assert pin(r['source']['path'])==r['source']
    equal=canonical.is_file() and body(canonical)==body(r['source']['path'])
    results.append({'module':name,'compiled_source':r['source'],'compiled_object':r['object'],
        'canonical_source':pin(canonical) if canonical.is_file() else None,
        'same_declaration_body':equal,
        'declaration_body_sha256':hashlib.sha256(body(r['source']['path']).encode()).hexdigest()})
review={'kind':'MAINTAINED_CANONICAL_DECLARATION_SOURCE_IDENTITY_REVIEW',
    'recipe':pin(Path(__file__)),'original_closure':pin(original_path),'modules':results,
    'all_match':all(r['same_declaration_body'] for r in results),
    'scope':'Comparison removes only blank lines and type/axiom reporting directives. Exact maintained declaration bodies, not compiled-object equivalence or new kernel/native refinement credit.'}
(ROOT/'review.json').write_text(json.dumps(review,separators=(',',':'),sort_keys=True)+'\n')
print(json.dumps({'modules':len(results),'all_match':review['all_match'],
    'mismatches':[r['module'] for r in results if not r['same_declaration_body']], 'review':pin(ROOT/'review.json')}))
