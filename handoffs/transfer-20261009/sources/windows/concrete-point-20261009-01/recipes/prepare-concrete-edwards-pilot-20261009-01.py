from pathlib import Path
import hashlib,subprocess,sys
local=Path('C:/src/shieldd-transfer-handoffs');diag=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
stem='windows-concrete-edwards-20261009-01';root='ConcreteEdwardsParameters01'
inspection=local/'concrete-edwards-closure-inspection-20261009-01.json'
assert inspection.exists()
composer=local/'compose-concrete-edwards-cache-20261009-01.py'
body=(local/'compose-field-cache-20261009-07.py').read_text().replace('windows-field-concrete-20261009-01',stem)
body=body.replace('field-concrete-closure-inspection-20261009-01.json',inspection.name)
assert not composer.exists();composer.write_bytes(body.encode());digest=hashlib.sha256(composer.read_bytes()).hexdigest()
preparer=local/('prepare-'+stem+'.py')
body=(local/'prepare-windows-field-concrete-20261009-01.py').read_text().replace('windows-field-concrete-20261009-01',stem).replace('ConcreteJubjubField01',root)
old="for namespace in ['windows-field-certificate-tree-20261009-03'"
new="for namespace in ['windows-edwards-equivalence-20261009-02','windows-edwards-map-20261009-05','windows-edwards-algebra-20261009-02','windows-field-concrete-20261009-01','windows-field-certificate-tree-20261009-03'"
assert old in body;body=body.replace(old,new)
body=body.replace("assert {'FieldPrimeNode38', 'ModularPower', 'LucasCertificate', 'UpstreamLucasPrimality'} <= {item['name'] for item in reused}", "assert {'ConcreteJubjubField01','EdwardsWeierstrassEquiv01'} <= {item['name'] for item in reused}")
scope='Concrete mathematical Parameters over certified ZMod Scalar.modulus, d nonzero, A40962 B-40964 exact parameter equations, displayed discriminant integer identity, bound and field nonzero. Mathlib Point/discriminant interpretation, addition, StandardCurveModel, cardinality and native representation OPEN.'
start=body.index('scope = ');end=body.index('\nmanifest = ',start);body=body[:start]+'scope = '+repr(scope)+body[end:]
body=body.replace("'parent_commit': 'e90e824285275bd59eac9fb1f5d173b9e38b0d17'", "'parent_commit': 'd90ffc4950623e68ed64d6d0200ea0f5d93da9ec'")
body=body.replace("names = re.findall(r'^theorem\\s+(\\w+)', body, re.M)","names = re.findall(r'^(?:theorem|(?:noncomputable )?def)\\s+(\\w+)', body, re.M)")
body=body.replace('compose-field-cache-20261009-07.py',composer.name).replace('4068d8b385e3e5755583a4ca11ddd62b853b4f13e2d9b33763be91d19151aa7c',digest)
assert not preparer.exists();preparer.write_bytes(body.encode());subprocess.run([sys.executable,str(preparer)],check=True)
helper=local/('run-safe-'+stem+'.ps1');guard=diag/('root-'+stem+'.ps1')
body=(local/'run-safe-windows-field-concrete-20261009-01.ps1').read_text().replace('windows-field-concrete-20261009-01',stem)
body=body.replace('safe-field-concrete-boundary-2026100901','safe-concrete-edwards-boundary-2026100901')
body=body.replace('e7d6f58261d9d362c4ef406f13c5c2d5edb8039d7e91bec30f3e09ef0c9aa12f',hashlib.sha256(guard.read_bytes()).hexdigest())
assert not helper.exists();helper.write_bytes(body.encode());print('Fresh concrete parameter pilot prepared; no proof credit yet')
