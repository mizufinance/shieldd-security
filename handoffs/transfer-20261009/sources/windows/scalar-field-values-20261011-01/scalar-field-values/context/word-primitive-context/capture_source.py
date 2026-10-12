"""Read existing source and optional cached crate; retain missing-metadata predecessor."""
import base64, hashlib, json, subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parent
assert not (ROOT/'context').exists()
code="import pathlib,json,base64,hashlib,tarfile; p=pathlib.Path('/root/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bls12_381-0.8.0/src/util.rs'); c=pathlib.Path('/root/.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f/bls12_381-0.8.0.crate'); b=p.read_bytes(); print(json.dumps({'source':str(p),'bytes':base64.b64encode(b).decode(),'cached_crate_sha256':hashlib.sha256(c.read_bytes()).hexdigest() if c.exists() else None,'cached_util_sha256':hashlib.sha256(tarfile.open(c).extractfile('bls12_381-0.8.0/src/util.rs').read()).hexdigest() if c.exists() else None}))"
result=subprocess.run(['wsl.exe','--','python3','-c',code],capture_output=True,timeout=90)
if result.returncode:
    print(result.stderr.decode(errors='replace'))
    raise RuntimeError('Read-only source copy failed')
record=json.loads(result.stdout)
b=base64.b64decode(record.pop('bytes'))
sha=hashlib.sha256(b).hexdigest()
lock=Path('C:/src/shieldd-pr160-844389ee/Cargo.lock').read_text()
section=next(s for s in lock.split('[[package]]') if '\nname = "bls12_381"\n' in s)
assert '\nversion = "0.8.0"\n' in section
if record['cached_crate_sha256']:
    assert '\nchecksum = "'+record['cached_crate_sha256']+'"\n' in section
    assert sha==record['cached_util_sha256']
record['package_archive_checksum_verified']=record['cached_crate_sha256'] is not None
(ROOT/'context').mkdir()
target=ROOT/'context/util.rs'; target.write_bytes(b)
record['copy']={'path':str(target),'bytes':len(b),'sha256':sha}
record['scope']='Read-only copy of existing registry source bytes. Cached archive authenticated against exact Cargo.lock when available; absence explicitly retained. Identity/source association only, not Rust semantic correspondence or runtime testing.'
(ROOT/'context/source-copy.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
print(json.dumps(record))
