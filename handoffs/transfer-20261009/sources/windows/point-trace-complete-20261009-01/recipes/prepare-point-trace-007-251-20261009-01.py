from pathlib import Path
import hashlib,json,re
local=Path('C:/src/shieldd-transfer-handoffs');diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
stem='windows-point-trace-007-251-20261009-01';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inspector=(local/'inspect-field-concrete-closure-20261009-01.py').read_text().replace('ShielddSecurity.ConcreteJubjubField01','ShielddSecurity.ConcretePointTraceStep251').replace('field-concrete-closure-inspection-20261009-01','point-trace-007-251-closure-inspection-20261009-01')
inspector=inspector.replace('out.write_bytes','assert not out.exists()\nout.write_bytes')
inspection_script=local/'inspect-point-trace-007-251-closure-20261009-01.py';assert not inspection_script.exists();inspection_script.write_text(inspector)
exec(compile(inspector,str(inspection_script),'exec'))
data=json.loads((local/'point-trace-007-251-closure-inspection-20261009-01.json').read_text());old=diag/'windows-jubjub-isolated-05/modules'
qualified=diag/'windows-concrete-point-20261009-05-kernel';records=json.loads((qualified/'qualified-external-identities.json').read_text());table={x['path']:x for x in records}
required={Path(x['path']).relative_to(old).as_posix() for x in data['files']}|{Path(p).relative_to(old).as_posix() for p in data['missing']}
assert required<=table.keys();size=sum(table[x]['bytes'] for x in required);assert size<=2*1024**3
composer_text=(local/'compose-concrete-point-cache-20261009-05.py').read_text()
composer_text=composer_text.replace('windows-concrete-point-20261009-05',stem).replace('concrete-point-closure-inspection-20261009-05.json','point-trace-007-251-closure-inspection-20261009-01.json')
start=composer_text.index("extra=local/");stop=composer_text.index("ids=json.loads",start)
composer_text=composer_text[:start]+f"qualified=diag/'windows-concrete-point-20261009-05-kernel'\nassert (qualified/'complete.txt').exists() and (qualified/'exit.txt').read_text().strip()=='0'\nidentities=qualified/'qualified-external-identities.json';known=json.loads(identities.read_text());table={{v['path']:v for v in known}}\nassert hashlib.sha256(identities.read_bytes()).hexdigest()=='{sha(qualified/'qualified-external-identities.json')}'\nrequired={{Path(v['path']).relative_to(old).as_posix() for v in data['files']}}|{{Path(p).relative_to(old).as_posix() for p in data['missing']}}\nassert required<=table.keys() and sum(table[p]['bytes'] for p in required)=={size}<=2*1024**3\n"+composer_text[stop:]
start=composer_text.index('inputs=[');stop=composer_text.index('for index,',start)
composer_text=composer_text[:start]+"inputs=[(qualified/'project'/p,Path(p),table[p]['bytes'],table[p]['sha256']) for p in sorted(required)]\n"+composer_text[stop:]
composer_text=re.sub(r'assert len\(records\)==\d+ and len\(data\[\x27sources\x27\]\)==\d+',f"assert len(records)=={len(required)} and len(data['sources'])=={len(data['sources'])}",composer_text)
composer_text=composer_text.replace("'copy_manifest_sha256':hashlib.sha256((extra/'manifest.json').read_bytes()).hexdigest()", "'qualified_prior_identities_sha256':hashlib.sha256(identities.read_bytes()).hexdigest()")
cp=local/'compose-point-trace-007-251-cache-20261009-01.py';assert not cp.exists();cp.write_text(composer_text)
body=(local/'prepare-windows-concrete-edwards-universe-types-20261009-01.py').read_text()
body=body.replace("stem = 'windows-concrete-edwards-20261009-01'",f"stem = '{stem}'").replace("for namespace in [","for namespace in ['windows-point-trace-003-006-20261009-01','windows-point-operation-pilot-20261009-04','windows-point-operation-pilot-20261009-01','windows-tangent-point-transport-20261009-01','windows-tangent-rational-20261009-01','windows-secant-point-transport-20261009-01','windows-secant-rational-20261009-02','windows-secant-polynomials-20261009-01','windows-pole-point-transport-20261009-02','windows-torsion-point-transport-20261009-03','windows-addition-helpers-20261009-01','windows-origin-addition-20261009-01','windows-addition-pilot-20261009-06','windows-point-operation-rows-20261009-03','windows-torsion-algebra-20261009-03','windows-concrete-point-20261009-05','windows-concrete-edwards-20261009-01',")
body=body.replace("visit('ConcreteEdwardsParameters01')","visit('ConcretePointTraceStep251')").replace("['ConcreteEdwardsParameters01']","['ConcretePointTraceStep251']")
body=body.replace("assert {'ConcreteJubjubField01','EdwardsWeierstrassEquiv01'} <=", "assert {'ConcreteWeierstrassPoint01'} <=")
scope='357 further actual Mathlib Point operations in candidate binary steps 007 through 251, consuming settled prefix 115 and small symbolic recurrences. Each named module has at most two operations, exact field certificates, derived output curve membership, and finite 300000 heartbeats/4096 recursion/1536MiB/240s. Final root proves exact r scalar annihilation; full 369-operation composition, exact point order, cardinality, native generator correspondence and full Transfer remain OPEN pending their separate audits.'
body=re.sub(r"scope = '[^\n]*'",'scope = '+repr(scope),body)
body=body[:body.index("old = diag / 'root-windows-graph-input-bridge")]
exec(compile(body,str(local/'prepare-torsion-point-transport-generated-20261009-01.py'),'exec'))
guard=(diag/'root-windows-concrete-point-20261009-05.ps1').read_text().replace('windows-concrete-point-20261009-05',stem).replace('compose-concrete-point-cache-20261009-05.py',cp.name).replace('012635eb06f645d97467ac20d2dc5243ab73153bced95c9f43373dc7b7444faf',sha(cp))
guard=re.sub(r"'Concrete certified field[^\n]*'\|Set-Content",repr(scope)+'|Set-Content',guard)
controller=diag/('root-'+stem+'.ps1');assert not controller.exists();controller.write_text(guard)
helper=(local/'run-safe-windows-concrete-point-20261009-05.ps1').read_text().replace('windows-concrete-point-20261009-05',stem).replace('safe-concrete-point-boundary-2026100905','safe-point-trace-007-251-boundary-2026100901').replace('TransferOwnedConcretePointBoundary2026100905','TransferOwnedPointTrace007251Boundary2026100901').replace('c6285829562d27f72269b4b6f3c71d4de992485897e35684767a917ddc6ab887',sha(controller))
hp=local/'run-safe-windows-point-trace-007-251-20261009-01.ps1';assert not hp.exists();hp.write_text(helper)
print(json.dumps({'bytes':size,'modules':len(data['sources']),'guard_sha256':sha(controller),'composer_sha256':sha(cp),'kernel_run':False}))
