"""Correct exact const-fn association after preserved setup-only spelling miss."""
from pathlib import Path
import shutil
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-scalar-wide-round-20261011-01'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir();shutil.copyfile(old/'handwritten/TransferScalarWideRound01.lean',ROOT/'handwritten/TransferScalarWideRound01.lean')
s=(old/'prepare_recipe.py').read_text().replace("text.index('    fn montgomery_reduce(')","text.index('    const fn montgomery_reduce(')")
s=s.replace('transfer-scalar-wide-round-owned-floor-20261011-01','transfer-scalar-wide-round-owned-floor-20261011-02')
s=s.replace("(ROOT/'prepare.py').write_text(s)","s=s.replace(\"plan['artifact_policy']\",\"plan['pins'] += [pin(DIAG/'transfer-scalar-wide-round-20261011-01/prepare_recipe.py'), pin(DIAG/'transfer-scalar-wide-round-20261011-01/handwritten/TransferScalarWideRound01.lean'), pin(ROOT/'recipe_source.py')]\\nplan['artifact_policy']\",1)\n(ROOT/'prepare.py').write_text(s)")
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'),{'__file__':str(ROOT/'recipe_source.py'),'__name__':'__main__'})
