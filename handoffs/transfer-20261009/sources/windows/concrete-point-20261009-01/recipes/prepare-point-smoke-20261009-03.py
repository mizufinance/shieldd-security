from pathlib import Path
import hashlib,json,re,ast
local=Path('C:/src/shieldd-transfer-handoffs')
diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
stem='windows-point-smoke-20261009-03'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
composer=local/'compose-point-smoke-cache-20261009-01.py'
composer.write_text('''from pathlib import Path
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
(stage.parent/'external-overlay.json').write_text(json.dumps(receipt,indent=2)+'\\n');(stage.parent/'qualified-external-identities.json').write_text(json.dumps(records,indent=2)+'\\n');print(json.dumps(receipt))
''')
body=(local/'prepare-windows-concrete-edwards-20261009-01.py').read_text()
begin=body.index("for namespace in [");end=body.index('\nstrip =',begin)
body=body[:begin]+body[end:]
body=body.replace("stem = 'windows-concrete-edwards-20261009-01'",f"stem = '{stem}'")
body=body.replace("visit('ConcreteEdwardsParameters01')","visit('MathlibPointImportSmoke01')")
body=body.replace("assert {'ConcreteJubjubField01','EdwardsWeierstrassEquiv01'} <= {item['name'] for item in reused}","assert not reused")
body=body.replace("names = re.findall(r'^(?:theorem|(?:noncomputable )?def)\\s+(\\w+)', body, re.M)","names = re.findall(r'^(?:theorem|(?:noncomputable )?def)\\s+(\\w+)', body, re.M) + ['WeierstrassCurve.Affine.Point.mk','WeierstrassCurve.Affine.pointEquiv','WeierstrassCurve.Affine.Point.neg','WeierstrassCurve.Affine.Point.instAddCommGroup']")
scope='One fresh Point import smoke module: two local group-law wrappers plus four full-type/axiom audits of pinned cached Mathlib declarations. No fresh Mathlib replay, Edwards Point join, addition compatibility, cardinality or native representation credit.'
body=re.sub(r"scope = '[^\n]*'",'scope = '+repr(scope),body)
body=body.replace("['ConcreteEdwardsParameters01']","['MathlibPointImportSmoke01']")
cut=body.index("old = diag / 'root-windows-graph-input-bridge");body=body[:cut]
exec(compile(body,str(local/'prepare-point-smoke-20261009-03.py'),'exec'))
auditor=diag/('audit-'+stem+'.py')
audit_body=auditor.read_text()
old_pattern="re.escape(full)+r'\\s*:'"
new_pattern="re.escape(full)+r'(?:\\.\\{[^}\\n]*\\})?\\s*:'"
assert old_pattern in audit_body
auditor.write_text(audit_body.replace(old_pattern,new_pattern))
guard=(diag/'root-windows-concrete-edwards-20261009-01.ps1').read_text()
guard=guard.replace('windows-concrete-edwards-20261009-01',stem).replace('compose-concrete-edwards-cache-20261009-01.py',composer.name).replace('e0690ab24ce9d2729df60ebc8fc35890ce0eb2ade1b7c1140b34c0ea4daaa31d',sha(composer))
guard=guard.replace('$env:LEAN_PATH="$taskStage;$taskExternal"','$env:LEAN_PATH="$taskStage"')
oldscope=re.search(r"'Concrete mathematical Parameters[^\n]*'\|Set-Content",guard).group(0)
guard=guard.replace(oldscope,repr(scope)+'|Set-Content')
controller=diag/('root-'+stem+'.ps1');assert not controller.exists();controller.write_text(guard)
helper=(local/'run-safe-windows-concrete-edwards-20261009-01.ps1').read_text().replace('windows-concrete-edwards-20261009-01',stem).replace('safe-concrete-edwards-boundary-2026100901','safe-point-smoke-boundary-2026100903').replace('TransferOwnedFieldConcreteBoundary2026100901','TransferOwnedPointSmokeBoundary2026100903').replace('9dc79979ecab3c24934a84d5aea0b9e6a77ccdcf3bfcc64cf67dd4a52134a79e',sha(controller))
(local/'run-safe-windows-point-smoke-20261009-03.ps1').write_text(helper)
print(json.dumps({'guard_sha256':sha(controller),'composer_sha256':sha(composer),'kernel_run':False}))
