import ast
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
p = DIAG / 'transfer-external-package-overlay-20261010-02/prepare.py'
s = p.read_text().replace("if module.startswith('Mathlib.NumberTheory.') and module.count('.') == 2:", "if (module.startswith('Mathlib.NumberTheory.') and module.count('.') == 2) or (module.startswith('Mathlib.') and module.count('.') == 1):")
s = s.replace('dst = nt / src.name;', 'dst = (dest if module.count(".") == 1 else nt) / src.name;')
s = s.replace('assert len(created) == 9', 'assert len(created) == 13').replace('nine exact', 'thirteen exact').replace('nine new', 'thirteen new')
ast.parse(s); (ROOT / 'prepare.py').write_text(s)
p = DIAG / 'transfer-external-floor-complete-20261010-07/prepare.py'
s = p.read_text().replace('transfer-external-package-overlay-20261010-02', 'transfer-external-package-overlay-20261010-03')
ast.parse(s); (DIAG / 'transfer-external-floor-complete-20261010-08/prepare.py').write_text(s)
for p in [DIAG / 'transfer-torsion-prime-nonsquare-20261010-03/prepare_repair.py', DIAG / 'transfer-prime-tree-replay-20261010-02/prepare.py']:
    s = p.read_text().replace('transfer-external-floor-complete-20261010-07', 'transfer-external-floor-complete-20261010-08').replace('transfer-external-package-overlay-20261010-02', 'transfer-external-package-overlay-20261010-03')
    ast.parse(s); p.write_text(s)
print('Fresh recipes include Mathlib.Init; all old partial artifacts preserved.')
