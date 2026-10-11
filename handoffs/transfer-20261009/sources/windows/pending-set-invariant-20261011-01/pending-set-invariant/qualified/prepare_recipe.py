"""Fresh preparation-only successor; no previous plan or Lean job admitted."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
ORIGINAL=DIAG/'transfer-pending-set-invariant-20261011-01'
assert not (ROOT/'prepare.py').exists()
source=ORIGINAL/'handwritten/TransferPendingSetInvariant01.lean'
target=ROOT/'handwritten/TransferPendingSetInvariant01.lean'
target.parent.mkdir(parents=True)
target.write_bytes(source.read_bytes())
recipe=(ORIGINAL/'prepare_recipe.py').read_text()
assert recipe.count('start=s.index("mapping = ")')==1
recipe=recipe.replace('start=s.index("mapping = ")','start=s.index("\\nmapping = ")+1')
recipe=recipe.replace('transfer-pending-set-invariant-owned-floor-20261011-01','transfer-pending-set-invariant-owned-floor-20261011-02')
recipe=recipe.replace("(ROOT/'prepare.py').write_text(s)","""needle="plan['pins'] += mapping['runtime_sources']"
assert s.count(needle)==1
s=s.replace(needle, "stopped_prepare = DIAG / 'transfer-pending-set-invariant-20261011-01'\\nplan['pins'] += [pin(stopped_prepare / n) for n in ['prepare_recipe.py', 'prepare.py', 'handwritten/TransferPendingSetInvariant01.lean', 'project/ShielddSecurity/TransferPendingSetInvariant01.lean']]\\nplan['pins'].append(pin(DIAG / 'transfer-pending-set-invariant-owned-floor-20261011-01/composition-review.json'))\\n"+needle)
(ROOT/'prepare.py').write_text(s)""")
exec(compile(recipe,str(ROOT/'prepare_recipe.py')+'<derived-fixed-selector>','exec'),globals())
