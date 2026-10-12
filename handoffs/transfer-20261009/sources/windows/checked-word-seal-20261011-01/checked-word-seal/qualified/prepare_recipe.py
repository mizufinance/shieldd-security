from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-checked-word-seal-20261011-02'
assert not (ROOT/'prepare.py').exists()
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-checked-word-seal-owned-floor-20261011-02'","POOL = DIAG / 'transfer-checked-word-seal-owned-floor-20261011-03'")
at=s.index("plan['artifact_policy'] = ")
files=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/checked-word-seal-shape.json','handwritten/TransferCheckedWordSeal01.lean','project/ShielddSecurity/TransferCheckedWordSeal01.lean','rejected-object-identity.json']
stdout='runs/01-TransferCheckedWordSeal01/stdout.txt'
if (OLD/stdout).exists(): files.append(stdout)
s=s[:at]+"pressureSeal=DIAG/'transfer-checked-word-seal-20261011-02'\nplan['pins'] += [pin(pressureSeal/n) for n in "+repr(files)+"]\n"+s[at:]
(ROOT/'handwritten').mkdir();(ROOT/'context').mkdir()
for name in ['handwritten/TransferCheckedWordSeal01.lean','context/checked-word-seal-shape.json','rejected-object-identity.json']:
    (ROOT/name).write_bytes((OLD/name).read_bytes())
(ROOT/'prepare.py').write_text(s)
print({'same_source_after_pressure':True,'failed_raw_files':len(files),'guards_unchanged':True})
