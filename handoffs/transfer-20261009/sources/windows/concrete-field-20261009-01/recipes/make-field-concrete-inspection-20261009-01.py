from pathlib import Path
local=Path('C:/src/shieldd-transfer-handoffs')
body=(local/'inspect-field-external-closure-20261009-01.py').read_text()
old="    matches=[p/Path(name.replace('.','/')).with_suffix('.lean') for p in roots]"
new="""    if name.startswith('ShielddSecurity.'):
        short=name.split('.',1)[1]
        choices=[Path('C:/src/shieldd-transfer-windows-publication-20261009/circuits/ShielddSecurity')/(short+'.lean'),
                 Path('C:/src/shieldd-transfer-handoffs/field-certificate-tree-20261009-01/ShielddSecurity')/(short+'.lean'),
                 Path('C:/src/shieldd-formal/circuits/ShielddSecurity')/(short+'.lean')]
        matches=[next(p for p in choices if p.exists())]
    else:
        matches=[p/Path(name.replace('.','/')).with_suffix('.lean') for p in roots]"""
assert old in body;body=body.replace(old,new)
body=body.replace("    if name=='Mathlib.NumberTheory.LucasPrimality':return", "    if name=='Mathlib.NumberTheory.LucasPrimality' or name.startswith('ShielddSecurity.'):return")
body=body.replace("['Mathlib.Data.ZMod.Basic','Mathlib.NumberTheory.LucasPrimality']", "['ShielddSecurity.ConcreteJubjubField01']")
body=body.replace('field-external-closure-inspection-20261009-01.json','field-concrete-closure-inspection-20261009-01.json')
(local/'inspect-field-concrete-closure-20261009-01.py').write_bytes(body.encode())
