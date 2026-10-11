"""Fresh retry after pressure stop; same source and strict runner."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-byte-key-cache-20261011-02'
s=(old/'prepare_recipe.py').read_text().replace('transfer-byte-key-cache-owned-floor-20261011-02','transfer-byte-key-cache-owned-floor-20261011-03')
exec(compile(s,str(old/'prepare_recipe.py'),'exec'),{'__file__':str(ROOT/'prepare_recipe.py'),'__name__':'__main__'})
assert (ROOT/'handwritten/TransferByteKeyCache01.lean').read_bytes()==(old/'handwritten/TransferByteKeyCache01.lean').read_bytes()
p=ROOT/'prepare.py';s=p.read_text();at=s.index("plan['artifact_policy']")
s=s[:at]+"pressureByteKey=DIAG/'transfer-byte-key-cache-20261011-02'\nplan['pins'] += [pin(pressureByteKey/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferByteKeyCache01.lean','project/ShielddSecurity/TransferByteKeyCache01.lean','runs/01-TransferByteKeyCache01/stdout.txt']]\n"+s[at:]
p.write_text(s)
