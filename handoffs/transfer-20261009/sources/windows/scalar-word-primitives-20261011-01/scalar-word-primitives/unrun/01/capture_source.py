"""Copy existing registry source bytes read-only; no downloads or runtime jobs."""
import base64, hashlib, json, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
assert not (ROOT/'context').exists()
code="import pathlib,json,base64; p=pathlib.Path('/root/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bls12_381-0.8.0'); print(json.dumps({n:base64.b64encode((p/n).read_bytes()).decode() for n in ['src/util.rs','.cargo-checksum.json']}))"
result=subprocess.run(['wsl.exe','--','python3','-c',code],capture_output=True,timeout=90,check=True)
data={n:base64.b64decode(b) for n,b in json.loads(result.stdout).items()}
checksum=json.loads(data['.cargo-checksum.json'])
assert hashlib.sha256(data['src/util.rs']).hexdigest()==checksum['files']['src/util.rs']
lock=Path('C:/src/shieldd-pr160-844389ee/Cargo.lock').read_text()
section=next(s for s in lock.split('[[package]]') if '\nname = "bls12_381"\n' in s)
assert '\nversion = "0.8.0"\n' in section
assert '\nchecksum = "'+checksum['package']+'"\n' in section
(ROOT/'context').mkdir()
rows=[]
for name,b in data.items():
    target=ROOT/'context'/Path(name).name
    target.write_bytes(b)
    rows.append({'path':str(target),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
record={'sources':rows,'registry':'bls12_381-0.8.0','package_checksum':checksum['package'],'util_source_checksum_verified':True,'cargo_lock_identity_verified':True,'scope':'Read-only copy of existing registry bytes plus Cargo checksum metadata. Identity and source association only, not primitive semantic correspondence or runtime testing.'}
(ROOT/'context/source-copy.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps(record))
