from pathlib import Path
import hashlib,json,re
local=Path('C:/src/shieldd-transfer-handoffs');diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
stem='windows-addition-pilot-20261009-06';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inspector=(local/'inspect-field-concrete-closure-20261009-01.py').read_text().replace('ShielddSecurity.ConcreteJubjubField01','ShielddSecurity.ConcretePointAdditionPilot01').replace('field-concrete-closure-inspection-20261009-01','addition-pilot-closure-inspection-20261009-06')
inspector=inspector.replace('out.write_bytes','assert not out.exists()\nout.write_bytes')
inspection_script=local/'inspect-addition-pilot-closure-20261009-06.py';assert not inspection_script.exists();inspection_script.write_text(inspector)
exec(compile(inspector,str(inspection_script),'exec'))
data=json.loads((local/'addition-pilot-closure-inspection-20261009-06.json').read_text());old=diag/'windows-jubjub-isolated-05/modules'
qualified=diag/'windows-concrete-point-20261009-05-kernel';records=json.loads((qualified/'qualified-external-identities.json').read_text());table={x['path']:x for x in records}
required={Path(x['path']).relative_to(old).as_posix() for x in data['files']}|{Path(p).relative_to(old).as_posix() for p in data['missing']}
assert required<=table.keys();size=sum(table[x]['bytes'] for x in required);assert size<=2*1024**3
composer_text=(local/'compose-concrete-point-cache-20261009-05.py').read_text()
composer_text=composer_text.replace('windows-concrete-point-20261009-05',stem).replace('concrete-point-closure-inspection-20261009-05.json','addition-pilot-closure-inspection-20261009-06.json')
start=composer_text.index("extra=local/");stop=composer_text.index("ids=json.loads",start)
composer_text=composer_text[:start]+f"qualified=diag/'windows-concrete-point-20261009-05-kernel'\nassert (qualified/'complete.txt').exists() and (qualified/'exit.txt').read_text().strip()=='0'\nidentities=qualified/'qualified-external-identities.json';known=json.loads(identities.read_text());table={{v['path']:v for v in known}}\nassert hashlib.sha256(identities.read_bytes()).hexdigest()=='{sha(qualified/'qualified-external-identities.json')}'\nrequired={{Path(v['path']).relative_to(old).as_posix() for v in data['files']}}|{{Path(p).relative_to(old).as_posix() for p in data['missing']}}\nassert required<=table.keys() and sum(table[p]['bytes'] for p in required)=={size}<=2*1024**3\n"+composer_text[stop:]
start=composer_text.index('inputs=[');stop=composer_text.index('for index,',start)
composer_text=composer_text[:start]+"inputs=[(qualified/'project'/p,Path(p),table[p]['bytes'],table[p]['sha256']) for p in sorted(required)]\n"+composer_text[stop:]
composer_text=re.sub(r'assert len\(records\)==\d+ and len\(data\[\x27sources\x27\]\)==\d+',f"assert len(records)=={len(required)} and len(data['sources'])=={len(data['sources'])}",composer_text)
composer_text=composer_text.replace("'copy_manifest_sha256':hashlib.sha256((extra/'manifest.json').read_bytes()).hexdigest()", "'qualified_prior_identities_sha256':hashlib.sha256(identities.read_bytes()).hexdigest()")
cp=local/'compose-addition-pilot-cache-20261009-06.py';assert not cp.exists();cp.write_text(composer_text)
body=(local/'prepare-windows-concrete-edwards-20261009-01.py').read_text()
body=body.replace("stem = 'windows-concrete-edwards-20261009-01'",f"stem = '{stem}'").replace("for namespace in [","for namespace in ['windows-concrete-point-20261009-05','windows-concrete-edwards-20261009-01',")
body=body.replace("visit('ConcreteEdwardsParameters01')","visit('ConcretePointAdditionPilot01')").replace("['ConcreteEdwardsParameters01']","['ConcretePointAdditionPilot01']")
body=body.replace("assert {'ConcreteJubjubField01','EdwardsWeierstrassEquiv01'} <=", "assert {'ConcreteWeierstrassPoint01'} <=")
scope='Bounded addition pilot: Edwards subtype closure and identity/commutativity/inverse/torsion formulas; concrete Mathlib negation transport and identity/inverse addition images. General secant/tangent/torsion addition transport, StandardCurveModel, order and native codec OPEN.'
body=re.sub(r"scope = '[^\n]*'",'scope = '+repr(scope),body)
body=body[:body.index("old = diag / 'root-windows-graph-input-bridge")]
exec(compile(body,str(local/'prepare-addition-pilot-20261009-06.py'),'exec'))
guard=(diag/'root-windows-concrete-point-20261009-05.ps1').read_text().replace('windows-concrete-point-20261009-05',stem).replace('compose-concrete-point-cache-20261009-05.py',cp.name).replace('012635eb06f645d97467ac20d2dc5243ab73153bced95c9f43373dc7b7444faf',sha(cp))
guard=re.sub(r"'Concrete certified field[^\n]*'\|Set-Content",repr(scope)+'|Set-Content',guard)
assert "  $taskMemory=Get-TaskMemorySnapshot\n  if($taskMemory.PhysicalKiB -lt 3145728 -or $taskMemory.CommitFreeKiB -lt 2621440){throw 'memory admission required'}" in guard
guard=guard.replace("  $taskMemory=Get-TaskMemorySnapshot\n  if($taskMemory.PhysicalKiB -lt 3145728 -or $taskMemory.CommitFreeKiB -lt 2621440){throw 'memory admission required'}","  $taskAdmissionStart=[DateTime]::UtcNow\n  while($true){\n   $taskMemory=Get-TaskMemorySnapshot\n   if($taskMemory.PhysicalKiB -ge 3145728 -and $taskMemory.CommitFreeKiB -ge 2621440){break}\n   if(([DateTime]::UtcNow-$taskAdmissionStart).TotalSeconds -ge 60){throw 'finite 60s admission wait expired; unchanged admission required'}\n   Start-Sleep -Milliseconds 400\n  }")
guard=guard.replace('finite_seconds_per_module=240','finite_seconds_per_module=240;admission_wait_seconds=60')
controller=diag/('root-'+stem+'.ps1');assert not controller.exists();controller.write_text(guard)
helper=(local/'run-safe-windows-concrete-point-20261009-05.ps1').read_text().replace('windows-concrete-point-20261009-05',stem).replace('safe-concrete-point-boundary-2026100905','safe-addition-pilot-boundary-2026100906').replace('TransferOwnedConcretePointBoundary2026100905','TransferOwnedAdditionPilotBoundary2026100906').replace('c6285829562d27f72269b4b6f3c71d4de992485897e35684767a917ddc6ab887',sha(controller))
hp=local/'run-safe-windows-addition-pilot-20261009-06.ps1';assert not hp.exists();hp.write_text(helper)
print(json.dumps({'bytes':size,'modules':len(data['sources']),'guard_sha256':sha(controller),'composer_sha256':sha(cp),'kernel_run':False}))
