from pathlib import Path
import hashlib,json,re
local=Path('C:/src/shieldd-transfer-handoffs');diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
stem='windows-concrete-point-20261009-03';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inspector=(local/'inspect-field-concrete-closure-20261009-01.py').read_text().replace('ShielddSecurity.ConcreteJubjubField01','ShielddSecurity.ConcreteWeierstrassPoint01').replace('field-concrete-closure-inspection-20261009-01','concrete-point-closure-inspection-20261009-01')
inspector=inspector.replace("out.write_bytes", "assert not out.exists()\nout.write_bytes")
(local/'inspect-concrete-point-closure-20261009-03.py').write_text(inspector);exec(compile(inspector,str(local/'inspect-concrete-point-closure-20261009-03.py'),'exec'))
data=json.loads((local/'concrete-point-closure-inspection-20261009-01.json').read_text());extra=json.loads((local/'point-qualified-companions-20261009-02/manifest.json').read_text());old=diag/'windows-jubjub-isolated-05/modules'
missing={Path(p).relative_to(old).as_posix() for p in data['missing']}
assert missing=={v['relative'] for v in extra['files']}
external_sources={k:v for k,v in data['sources'].items() if not k.startswith('ShielddSecurity.') and k!='Mathlib.NumberTheory.LucasPrimality'}
assert data['bytes']+extra['bytes']<=2*1024**3
composer=(local/'compose-point-smoke-cache-20261009-01.py').read_text().replace('windows-point-smoke-20261009-01',stem).replace('edwards-point-closure-inspection-20261009-01.json','concrete-point-closure-inspection-20261009-01.json')
composer=composer.replace("assert data['bytes']+copied['bytes']==1420544576==copied['final_closure_bytes']",f"assert data['bytes']+copied['bytes']=={data['bytes']+extra['bytes']}")
composer=composer.replace("assert len(records)==7724 and len(data['sources'])==1931",f"assert len(records)=={len(data['files'])+272} and len(data['sources'])=={len(data['sources'])}")
composer=composer.replace("assert copied['final_closure_bytes']<=2*1024**3","assert data['bytes']+copied['bytes']<=2*1024**3")
cp=local/'compose-concrete-point-cache-20261009-03.py';cp.write_text(composer)
body=(local/'prepare-windows-concrete-edwards-20261009-01.py').read_text().replace("stem = 'windows-concrete-edwards-20261009-01'",f"stem = '{stem}'").replace("for namespace in [","for namespace in ['windows-concrete-edwards-20261009-01',")
body=body.replace("visit('ConcreteEdwardsParameters01')","visit('ConcreteWeierstrassPoint01')").replace("['ConcreteEdwardsParameters01']","['ConcreteWeierstrassPoint01']")
body=body.replace("assert {'ConcreteJubjubField01','EdwardsWeierstrassEquiv01'} <=", "assert {'ConcreteEdwardsParameters01'} <=")
scope='Concrete certified field and parameters instantiate Mathlib affine curve: exact discriminant, ellipticity, full Edwards point-set bijection and exceptional identity/torsion images. Addition homomorphism, StandardCurveModel, cardinality, full curve order and native representation OPEN.'
body=re.sub(r"scope = '[^\n]*'",'scope = '+repr(scope),body)
body=body[:body.index("old = diag / 'root-windows-graph-input-bridge")]
exec(compile(body,str(local/'prepare-concrete-point-20261009-03.py'),'exec'))
guard=(diag/'root-windows-concrete-edwards-20261009-01.ps1').read_text().replace('windows-concrete-edwards-20261009-01',stem).replace('compose-concrete-edwards-cache-20261009-01.py',cp.name).replace('e0690ab24ce9d2729df60ebc8fc35890ce0eb2ade1b7c1140b34c0ea4daaa31d',sha(cp))
oldscope=re.search(r"'Concrete mathematical Parameters[^\n]*'\|Set-Content",guard).group(0);guard=guard.replace(oldscope,repr(scope)+'|Set-Content')
guard=guard.replace('$env:LEAN_PATH="$taskStage;$taskExternal"','$env:LEAN_PATH="$taskStage"')
controller=diag/('root-'+stem+'.ps1');assert not controller.exists();controller.write_text(guard)
helper=(local/'run-safe-windows-concrete-edwards-20261009-01.ps1').read_text().replace('windows-concrete-edwards-20261009-01',stem).replace('safe-concrete-edwards-boundary-2026100901','safe-concrete-point-boundary-2026100903').replace('TransferOwnedFieldConcreteBoundary2026100901','TransferOwnedConcretePointBoundary2026100903').replace('9dc79979ecab3c24934a84d5aea0b9e6a77ccdcf3bfcc64cf67dd4a52134a79e',sha(controller))
(local/'run-safe-windows-concrete-point-20261009-03.ps1').write_text(helper)
print(json.dumps({'closure_bytes':data['bytes']+extra['bytes'],'guard_sha256':sha(controller),'kernel_run':False}))
