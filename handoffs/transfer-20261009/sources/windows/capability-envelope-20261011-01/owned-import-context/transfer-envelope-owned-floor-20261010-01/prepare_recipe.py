"""Prepare one complete437-object first package root for the final framing join."""
import ast
from pathlib import Path
ROOT=Path(__file__).resolve().parent
PRIOR=ROOT.parent/'transfer-proof-admission-owned-floor-20261010-01'
text=(PRIOR/'prepare.py').read_text()
(ROOT/'predecessor_prepare.py').write_text(text,encoding='utf-8',newline='\n')
text=text.replace("          ('transfer-proof-admission-20261010-02', 1)]",
                  "          ('transfer-proof-admission-20261010-02', 1),\n          ('transfer-envelope-source-bridge-20261010-01', 1)]")
text=text.replace('assert len(selected) == 436','assert len(selected) == 437')
text=text.replace("'prior_complete_owned_floor': pin(DIAG / 'transfer-capability-owned-floor-20261010-01/composition-review.json')", "'prior_complete_owned_floor': pin(DIAG / 'transfer-proof-admission-owned-floor-20261010-01/composition-review.json')")
start=text.index("               'scope': ");end=text.index("}\npending =",start)
scope='Complete immutable first owned package root:384 retained objects plus53 concrete SDK/raw authorization, acceptance, constructive rows, local-registry admission and retained-envelope objects. Every copy fully charged under unchanged128MiB cap. Identity copying grants zero new proof, runtime, semantic correspondence or certification credit.'
text=text[:start]+"               'scope': "+repr(scope)+text[end:]
ast.parse(text)
assert not (ROOT/'prepare.py').exists()
(ROOT/'prepare.py').write_text(text,encoding='utf-8',newline='\n')
print('Complete437-object floor recipe prepared; successful Envelope qualification required.')
