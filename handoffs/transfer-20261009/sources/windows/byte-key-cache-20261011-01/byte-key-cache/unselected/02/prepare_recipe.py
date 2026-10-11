"""Fresh explicit function binder repair, seven contracts unchanged."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-byte-key-cache-20261011-01'
s=(old/'prepare_recipe.py').read_text()
a='⟨TransferInjectiveKeyPublication01.keyCode_is_injective, congrArg keyCode⟩'
b='⟨fun same => TransferInjectiveKeyPublication01.keyCode_is_injective same, fun same => congrArg keyCode same⟩'
assert s.count(a)==1;s=s.replace(a,b).replace('transfer-byte-key-cache-owned-floor-20261011-01','transfer-byte-key-cache-owned-floor-20261011-02')
(ROOT/'recipe_source.py').write_text(s)
exec(compile(s,str(ROOT/'recipe_source.py'),'exec'),{'__file__':str(ROOT/'recipe_source.py'),'__name__':'__main__'})
p=ROOT/'prepare.py';s=p.read_text();a="[Path(__file__), ROOT / 'prepare_recipe.py', runner";assert s.count(a)==1
s=s.replace(a,"[Path(__file__), ROOT / 'prepare_recipe.py', ROOT / 'recipe_source.py', runner")
at=s.index("plan['artifact_policy']")
s=s[:at]+"failedByteKey=DIAG/'transfer-byte-key-cache-20261011-01'\nplan['pins'] += [pin(failedByteKey/n) for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferByteKeyCache01.lean','project/ShielddSecurity/TransferByteKeyCache01.lean','runs/01-TransferByteKeyCache01/stdout.txt']]\n"+s[at:]
p.write_text(s)
