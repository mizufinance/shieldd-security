"""Prepare a complete436-object floor for the retained-envelope join."""
import ast
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PRIOR=ROOT.parent/'transfer-capability-owned-floor-20261010-01'
text=(PRIOR/'prepare.py').read_text()
(ROOT/'predecessor_prepare.py').write_text(text,encoding='utf-8',newline='\n')
text=text.replace("          ('transfer-capability-acceptance-20261010-03', 1)]",
                  "          ('transfer-capability-acceptance-20261010-03', 1),\n          ('transfer-capability-rows-20261010-01', 1),\n          ('transfer-proof-admission-20261010-02', 1)]")
text=text.replace('assert len(selected) == 434','assert len(selected) == 436')
text=text.replace("'prior_complete_owned_floor': pin(DIAG / 'transfer-sdk-raw-authorization-floor-20261010-01/composition-review.json')", "'prior_complete_owned_floor': pin(DIAG / 'transfer-capability-owned-floor-20261010-01/composition-review.json')")
start=text.index("               'scope': ");end=text.index("}\npending =",start)
scope='Complete immutable first owned package root:384 retained qualified objects plus52 concrete SDK/raw authorization and acceptance/constructive-row/registry-admission objects. Every copied object fully charged under unchanged128MiB cap; copies grant no new proof, semantic correspondence, runtime or certification credit.'
text=text[:start]+"               'scope': "+repr(scope)+text[end:]
ast.parse(text)
assert not (ROOT/'prepare.py').exists()
(ROOT/'prepare.py').write_text(text,encoding='utf-8',newline='\n')
print('Complete436-object floor recipe prepared; registry admission qualification required before copying.')
