from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent;old=DIAG/'transfer-nullifier-field-codec-20261012-01'
assert not (ROOT/'prepare.py').exists()
source=(old/'handwritten/TransferNullifierFieldCodec01.lean').read_text()
assert source.count('simp only [Vector.toList, List.toList_toArray, width, true_and]')==1
source=source.replace('simp only [Vector.toList, List.toList_toArray, width, true_and]','simp only [Vector.toList, width, true_and]')
before='  · simp only [sourceNullifierSliceDecode, dif_neg width, reduceCtorEq, exists_const,\n      width, false_and]'
assert source.count(before)==1
source=source.replace(before,'  · rw [sourceNullifierSliceDecode, dif_neg width]\n    simp only [reduceCtorEq, exists_const, width, false_and]')
assert source.count('simp only [Vector.toList, List.toList_toArray] at same')==1
source=source.replace('simp only [Vector.toList, List.toList_toArray] at same','simp only [Vector.toList] at same')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferNullifierFieldCodec01.lean').write_bytes(source.encode())
prep=(old/'prepare.py').read_text()
prep=prep.replace("POOL=DIAG/'transfer-nullifier-field-codec-owned-floor-20261012-01'","POOL=DIAG/'transfer-nullifier-field-codec-owned-floor-20261012-02'")
extra="""failed=DIAG/'transfer-nullifier-field-codec-20261012-01'
assert json.loads((failed/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
failed_files=sorted(p for p in failed.rglob('*') if p.is_file())
plan['pins'] += [pin(p) for p in failed_files]+[pin(ROOT/'prepare_from01.py')]
"""
at=prep.index("plan['artifact_policy']");prep=prep[:at]+extra+prep[at:]
(ROOT/'prepare.py').write_bytes(prep.encode())
print({'same10_statements':True,'repair':'dependent conditional rewritten before simplification; remove only reported unused simp arguments','all_failed_original_files_retained':True,'guards_unchanged':True})
