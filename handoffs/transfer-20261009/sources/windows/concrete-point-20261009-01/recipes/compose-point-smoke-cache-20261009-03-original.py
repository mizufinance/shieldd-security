from pathlib import Path
import hashlib,json,os,subprocess,sys,time
local=Path('C:/src/shieldd-transfer-handoffs');diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
stage=Path(sys.argv[1]).resolve();assert stage==(diag/'windows-point-smoke-20261009-03-kernel/project').resolve()
old=diag/'windows-jubjub-isolated-05/modules';cache=old.parent
inspection=local/'edwards-point-closure-inspection-20261009-01.json';data=json.loads(inspection.read_text())
extra=local/'point-qualified-companions-20261009-02';copied=json.loads((extra/'manifest.json').read_text())
assert data['bytes']+copied['bytes']==1420544576==copied['final_closure_bytes']
assert copied['final_closure_bytes']<=2*1024**3
ids=json.loads((cache/'inputs.json').read_text());packages=Path('C:/src/shieldd-formal/circuits/.lake/packages')
for name,commit in ids['packages'].items():
 p=packages/name;assert subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()==commit
 assert not subprocess.check_output(['git','-C',str(p),'status','--porcelain','--untracked-files=no'],text=True).strip()
for item in data['sources'].values():assert hashlib.sha256(Path(item['source']).read_bytes()).hexdigest()==item['sha256']
records=[];start=time.monotonic()
inputs=[(Path(v['path']),Path(v['path']).relative_to(old),v['bytes'],None) for v in data['files']]
inputs += [(extra/v['relative'],Path(v['relative']),v['bytes'],v['sha256']) for v in copied['files']]
for index,(p,relative,size,digest) in enumerate(inputs):
 assert time.monotonic()-start<240,'finite composition budget'
 if index%256==0:
  command=". 'C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002/native-host-memory-api-01.ps1'; Get-TaskMemorySnapshot | ConvertTo-Json -Compress"
  raw=subprocess.check_output(['C:/Users/acyrn/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe','-NoProfile','-NonInteractive','-Command',command],text=True,timeout=10)
  memory=json.loads(raw);assert memory['PhysicalKiB']>=1572864 and memory['CommitFreeKiB']>=524288
 assert p.stat().st_size==size;actual=hashlib.sha256(p.read_bytes()).hexdigest();assert digest is None or actual==digest
 target=stage/relative;assert not target.exists();target.parent.mkdir(parents=True,exist_ok=True);os.link(p,target)
 assert hashlib.sha256(target.read_bytes()).hexdigest()==actual
 records.append({'path':relative.as_posix(),'sha256':actual,'bytes':size})
assert len(records)==7724 and len(data['sources'])==1931
receipt={'kind':'Separate authorized <=2GiB exact pinned Point artifact closure; zero proof credit','files':len(records),'source_modules':len(data['sources']),'bytes':sum(v['bytes'] for v in records),'disk_cap_bytes':2*1024**3,'inspection_sha256':hashlib.sha256(inspection.read_bytes()).hexdigest(),'copy_manifest_sha256':hashlib.sha256((extra/'manifest.json').read_bytes()).hexdigest(),'identities_sha256':hashlib.sha256(json.dumps(records,sort_keys=True).encode()).hexdigest(),'producer_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(stage.parent/'external-overlay.json').write_text(json.dumps(receipt,indent=2)+'\n');(stage.parent/'qualified-external-identities.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps(receipt))
