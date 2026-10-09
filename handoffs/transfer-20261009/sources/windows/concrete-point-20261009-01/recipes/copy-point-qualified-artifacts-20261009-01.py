from pathlib import Path
import hashlib,json,shutil,subprocess,time
local=Path('/mnt/c/src/shieldd-transfer-handoffs');source=local/'point-artifact-stage-20261009-02/receipt.json'
data=json.loads(source.read_text());assert data['final_qualified_closure_bytes']<=2*1024**3
out=local/'point-qualified-companions-20261009-01';assert not out.exists();out.mkdir()
start=time.monotonic();records=[]
for index,item in enumerate(data['additional_artifacts']):
    assert time.monotonic()-start<90
    if index%32==0:
        command=". 'C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002/native-host-memory-api-01.ps1'; Get-TaskMemorySnapshot | ConvertTo-Json -Compress"
        raw=subprocess.check_output(['/mnt/c/Program Files/PowerShell/7/pwsh.exe','-NoProfile','-NonInteractive','-Command',command],text=True,timeout=10)
        memory=json.loads(raw);assert memory['PhysicalKiB']>=1572864 and memory['CommitFreeKiB']>=524288,'existing host reserves'
    relative=Path(item['relative']);assert not relative.is_absolute() and '..' not in relative.parts
    p=Path(item['path']);assert p.stat().st_size==item['bytes'] and hashlib.sha256(p.read_bytes()).hexdigest()==item['sha256']
    target=out/relative;target.parent.mkdir(parents=True,exist_ok=True);assert not target.exists();shutil.copyfile(p,target)
    assert hashlib.sha256(target.read_bytes()).hexdigest()==item['sha256']
    records.append({'relative':relative.as_posix(),'bytes':item['bytes'],'sha256':item['sha256']})
assert len(records)==272
receipt={'kind':'Exact qualified artifact copy, no import/proof credit','files':records,'bytes':sum(v['bytes'] for v in records),
 'source_receipt_sha256':hashlib.sha256(source.read_bytes()).hexdigest(),'final_closure_bytes':data['final_qualified_closure_bytes']}
(out/'manifest.json').write_bytes((json.dumps(receipt,indent=2)+'\n').encode())
print(json.dumps({k:receipt[k] for k in ['kind','bytes','final_closure_bytes']}))
