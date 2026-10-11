"""Read-only live source identity and exact overlay diff capture; no native job."""
from pathlib import Path
import difflib, hashlib, json
OUT = Path('/mnt/c/src/shieldd-formal/.work/diagnostics/transfer-runtime-overlay-review-20261010-01')
D = OUT.parent / 'transfer-implementation-20261002'
R = Path('/mnt/c/src/shieldd-pr160-844389ee')
SOURCE = Path('/root/.cache/shieldd-security-verification/transfer-coherent-controls-844389-20261004-09')
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for block in iter(lambda:f.read(1048576),b''):h.update(block)
    return h.hexdigest()
expected=json.loads((D/'transfer-coherent-controls-job-05-22/full-source-before.json').read_bytes())
actual={str(p.relative_to(SOURCE)):sha(p) for p in SOURCE.rglob('*') if p.is_file()}
assert actual==expected, ('live overlay source changed',sorted(set(actual)^set(expected)),
    [n for n in actual if n in expected and actual[n]!=expected[n]])
diffs=[]
for name, wanted in expected.items():
    base=R/name
    if not base.exists() or sha(base)!=wanted:
        old=base.read_text().splitlines(keepends=True) if base.exists() else []
        new=(SOURCE/name).read_text().splitlines(keepends=True)
        delta=''.join(difflib.unified_diff(old,new,fromfile='clean/'+name,tofile='overlay/'+name))
        target=OUT/'diffs'/Path(name+'.diff')
        assert not target.exists()
        target.parent.mkdir(parents=True,exist_ok=True)
        target.write_text(delta,encoding='utf-8')
        diffs.append(dict(path=name,base_sha256=sha(base) if base.exists() else None,
            overlay_sha256=wanted,diff_bytes=target.stat().st_size,diff_sha256=sha(target),
            added_lines=sum(line.startswith('+') and not line.startswith('+++') for line in delta.splitlines()),
            removed_lines=sum(line.startswith('-') and not line.startswith('---') for line in delta.splitlines())))
binary_records={}
for output in ['transfer-coherent-controls-job-02-22','transfer-coherent-controls-job-03-22']:
    for name, b in json.loads((D/output/'build-receipt.json').read_bytes())['binaries'].items():
        p=Path(b['path'])
        actual_sha=sha(p) if p.is_file() else None
        binary_records[name]=dict(**b,current_sha256=actual_sha,current_matches_receipt=actual_sha==b['sha256'])
report=dict(status='LIVE_OVERLAY_IDENTITY_AND_DIFF_CAPTURE',source_files=len(actual),
    source_matches_retained_inventory=True,differences=diffs,binaries=binary_records,
    native_jobs_launched=0,semantic_correspondence=False,certification=False)
target=OUT/'capture.json'
assert not target.exists()
target.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
print(json.dumps(dict(source_files=len(actual),differences=len(diffs),
    binary_current_matches={n:b['current_matches_receipt'] for n,b in binary_records.items()},
    capture_sha256=sha(target))))
