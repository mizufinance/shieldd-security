from pathlib import Path
import hashlib,json,os,sys
source=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002/windows-jubjub-isolated-05/modules')
stage=Path(sys.argv[1]).resolve()
expected=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002/windows-field-certificate-pilot-20261009-03-kernel/project').resolve()
assert stage==expected,'exact fresh diagnostic project required'
assert not (source/'Mathlib/NumberTheory/LucasPrimality.olean').exists()
files=sorted(p for p in source.rglob('*') if p.is_file())
assert sum(p.stat().st_size for p in files)<1024**3
records=[]
for p in files:
    target=stage/p.relative_to(source)
    assert not target.exists()
    target.parent.mkdir(parents=True,exist_ok=True)
    digest=hashlib.sha256(p.read_bytes()).hexdigest()
    os.link(p,target)
    assert hashlib.sha256(target.read_bytes()).hexdigest()==digest
    records.append({'path':str(p.relative_to(source)).replace('\\','/'),'sha256':digest})
receipt={'kind':'Read-only diagnostic hardlink overlay; no theorem credit',
         'files':len(records),'identities_sha256':hashlib.sha256(json.dumps(records,sort_keys=True).encode()).hexdigest(),
         'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(stage.parent/'external-overlay.json').write_bytes((json.dumps(receipt,indent=2)+'\n').encode())
print(json.dumps(receipt))
