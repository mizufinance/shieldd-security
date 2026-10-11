"""Fresh singleton compare case repair, all eight contracts unchanged."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-scalar-reversed-byte-order-20261011-01'
s=(old/'prepare_recipe.py').read_text()
a='    | nil => rfl';b='    | nil => cases compare lastLeft.toNat lastRight.toNat <;> rfl'
assert s.count(a)==2;s=s.replace(a,b,1).replace('transfer-scalar-reversed-byte-order-owned-floor-20261011-01','transfer-scalar-reversed-byte-order-owned-floor-20261011-02')
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'),{'__file__':str(ROOT/'recipe_source.py'),'__name__':'__main__'})
p=ROOT/'prepare.py';s=p.read_text();a="[Path(__file__), ROOT / 'prepare_recipe.py', runner";assert s.count(a)==1
s=s.replace(a,"[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner")
at=s.index("plan['artifact_policy']")
s=s[:at]+"failedReversed=DIAG/'transfer-scalar-reversed-byte-order-20261011-01'\nplan['pins'] += [pin(failedReversed/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarReversedByteOrder01.lean','project/ShielddSecurity/TransferScalarReversedByteOrder01.lean','runs/01-TransferScalarReversedByteOrder01/stdout.txt']]\n"+s[at:]
p.write_text(s)
