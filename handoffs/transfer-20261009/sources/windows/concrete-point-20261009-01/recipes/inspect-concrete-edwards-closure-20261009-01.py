from pathlib import Path
body=Path('C:/src/shieldd-transfer-handoffs/inspect-field-concrete-closure-20261009-01.py').read_text()
body=body.replace('ShielddSecurity.ConcreteJubjubField01','ShielddSecurity.ConcreteEdwardsParameters01')
body=body.replace('field-concrete-closure-inspection-20261009-01','concrete-edwards-closure-inspection-20261009-01')
exec(compile(body,__file__,'exec'))
