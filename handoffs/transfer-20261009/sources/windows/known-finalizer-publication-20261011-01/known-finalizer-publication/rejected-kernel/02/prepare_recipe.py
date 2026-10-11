"""Fresh setup repair: replace only current upstream stdout, retain failed setup."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-known-finalizer-publication-20261011-01'
s=(old/'prepare_recipe.py').read_text()
a='replace("\'runs/01-TransferSourceTypedInputProjection01/stdout.txt\'", "\'runs/01-TransferFinalizationObjectFrames01/stdout.txt\'")'
b='s=s.replace("\'runs/01-TransferSourceTypedInputProjection01/stdout.txt\'", "\'runs/01-TransferFinalizationObjectFrames01/stdout.txt\'",1)'
assert s.count(a)==1
s=s.replace(a,b)
s=s.replace('transfer-known-finalizer-publication-owned-floor-20261011-01','transfer-known-finalizer-publication-owned-floor-20261011-02')
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'),{'__file__':str(ROOT/'recipe_source.py'),'__name__':'__main__'})
p=ROOT/'prepare.py'; s=p.read_text()
a="[Path(__file__), ROOT / 'prepare_recipe.py', runner"
assert s.count(a)==1
s=s.replace(a,"[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner")
a="plan['artifact_policy']"
at=s.index(a)
s=s[:at]+"plan['pins'] += [pin(DIAG/'transfer-known-finalizer-publication-20261011-01/prepare_recipe.py'),pin(DIAG/'transfer-known-finalizer-publication-20261011-01/handwritten/TransferKnownFinalizerPublication01.lean')]\n"+s[at:]
p.write_text(s)
