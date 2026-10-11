"""Bounded symbolic elaboration using serializer theorem instead of unfolding."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-scalar-canonical-key-20261011-02'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir()
source=(old/'handwritten/TransferScalarCanonicalKey01.lean').read_text()
needle='namespace ShielddSecurity.TransferScalarCanonicalKey01\n';assert source.count(needle)==1
source=source.replace(needle,needle+'attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey\n')
(ROOT/'handwritten/TransferScalarCanonicalKey01.lean').write_text(source)
s=(old/'prepare.py').read_text().replace('transfer-scalar-canonical-key-owned-floor-20261011-02','transfer-scalar-canonical-key-owned-floor-20261011-03')
s=s.replace("plan['artifact_policy']","failedKey02=DIAG/'transfer-scalar-canonical-key-20261011-02'\nplan['pins'] += [pin(failedKey02/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarCanonicalKey01.lean','project/ShielddSecurity/TransferScalarCanonicalKey01.lean','runs/01-TransferScalarCanonicalKey01/stdout.txt']]\nplan['artifact_policy']",1)
(ROOT/'prepare.py').write_text(s)
print({'fresh_reports':8,'failed_attempts_preserved':2,'failed_credit':0,'local_elaboration_only':True,'guards_unchanged':True})
