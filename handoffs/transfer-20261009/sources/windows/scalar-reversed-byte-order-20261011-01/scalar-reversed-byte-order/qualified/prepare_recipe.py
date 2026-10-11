"""Expose singleton lexical recursion before the existing finite compare split."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-scalar-reversed-byte-order-20261011-02'
s=(old/'prepare_recipe.py').read_text()
a='    | nil => cases compare lastLeft.toNat lastRight.toNat <;> rfl'
b='    | nil => simp only [List.nil_append, compareHighFirst]; cases compare lastLeft.toNat lastRight.toNat <;> rfl'
assert s.count(a)==1;s=s.replace(a,b).replace('transfer-scalar-reversed-byte-order-owned-floor-20261011-02','transfer-scalar-reversed-byte-order-owned-floor-20261011-03')
exec(compile(s,str(old/'prepare_recipe.py'),'exec'),{'__file__':str(ROOT/'prepare_recipe.py'),'__name__':'__main__'})
p=ROOT/'prepare.py';s=p.read_text();at=s.index("plan['artifact_policy']")
s=s[:at]+"failedReversed02=DIAG/'transfer-scalar-reversed-byte-order-20261011-02'\nplan['pins'] += [pin(failedReversed02/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarReversedByteOrder01.lean','project/ShielddSecurity/TransferScalarReversedByteOrder01.lean','runs/01-TransferScalarReversedByteOrder01/stdout.txt']]\n"+s[at:]
p.write_text(s)
