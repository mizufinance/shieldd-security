from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-checked-word-seal-publication-20261011-01'
assert not (ROOT/'prepare.py').exists()
s=(OLD/'prepare.py').read_text().replace("POOL = DIAG / 'transfer-checked-word-seal-publication-owned-floor-20261011-01'","POOL = DIAG / 'transfer-checked-word-seal-publication-owned-floor-20261011-02'")
files=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCheckedWordSealPublication01.lean','project/ShielddSecurity/TransferCheckedWordSealPublication01.lean']
stdout='runs/01-TransferCheckedWordSealPublication01/stdout.txt'
if (OLD/stdout).exists():files.append(stdout)
at=s.index("plan['artifact_policy'] = ")
s=s[:at]+"pressureSealPublication=DIAG/'transfer-checked-word-seal-publication-20261011-01'\nplan['pins'] += [pin(pressureSealPublication/n) for n in "+repr(files)+"]\n"+s[at:]
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferCheckedWordSealPublication01.lean').write_bytes((OLD/'handwritten/TransferCheckedWordSealPublication01.lean').read_bytes())
(ROOT/'prepare.py').write_text(s)
print({'same_source_after_pressure':True,'failed_raw_files':len(files),'guards_unchanged':True})
