"""Prepare a complete434-object first package root; do not run before both passes."""
import ast
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PRIOR=ROOT.parent/'transfer-sdk-raw-authorization-floor-20261010-01'
text=(PRIOR/'prepare.py').read_text()
(ROOT/'predecessor_prepare.py').write_text(text,encoding='utf-8',newline='\n')
text=text.replace("          ('transfer-sdk-raw-authorization-20261010-01', 1)]",
                  "          ('transfer-sdk-raw-authorization-20261010-01', 1),\n          ('transfer-sdk-raw-authorization-join-20261010-02', 1),\n          ('transfer-capability-acceptance-20261010-03', 1)]")
text=text.replace('assert len(selected) == 432','assert len(selected) == 434')
text=text.replace("'unexecuted_reader_predecessor_recipe': pin(ROOT / 'predecessor_prepare01.py'),", "'prior_complete_owned_floor': pin(DIAG / 'transfer-sdk-raw-authorization-floor-20261010-01/composition-review.json'),\n               'predecessor_floor_recipe': pin(ROOT / 'predecessor_prepare.py'),")
start=text.index("               'scope': ");end=text.index("}\npending =",start)
scope='Complete immutable first owned package root:384 retained qualified objects plus50 qualified concrete arithmetic/SDK/raw authorization and transaction acceptance interfaces. All copies fully charged under unchanged128MiB cap. Copy identity gives no new proof, runtime, semantic correspondence or certification credit.'
text=text[:start]+"               'scope': "+repr(scope)+text[end:]
ast.parse(text)
assert not (ROOT/'prepare.py').exists()
(ROOT/'prepare.py').write_text(text,encoding='utf-8',newline='\n')
print('Complete434-object floor recipe prepared; qualified SDK endpoint and Acceptance03 passes required.')
