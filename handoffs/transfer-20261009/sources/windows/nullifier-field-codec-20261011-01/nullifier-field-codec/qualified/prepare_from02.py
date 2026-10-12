from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent;old=DIAG/'transfer-nullifier-field-codec-20261012-02'
assert not (ROOT/'prepare.py').exists()
source=(old/'handwritten/TransferNullifierFieldCodec01.lean').read_text()
assert source.count('simp only [reduceCtorEq, exists_const, width, false_and]')==1
source=source.replace('simp only [reduceCtorEq, exists_const, width, false_and]','simp only [reduceCtorEq, width, false_and]\n    constructor\n    · rintro ⟨scalar, impossible⟩; exact impossible\n    · intro impossible; exact False.elim impossible')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferNullifierFieldCodec01.lean').write_bytes(source.encode())
prep=(old/'prepare.py').read_text().replace("POOL=DIAG/'transfer-nullifier-field-codec-owned-floor-20261012-02'","POOL=DIAG/'transfer-nullifier-field-codec-owned-floor-20261012-03'")
prep=prep.replace("[pin(ROOT/'prepare_from01.py')]","[pin(ROOT/'prepare_from02.py')]")
extra="""failed_second=DIAG/'transfer-nullifier-field-codec-20261012-02'
assert json.loads((failed_second/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
plan['pins'] += [pin(p) for p in sorted(failed_second.rglob('*')) if p.is_file()]
"""
at=prep.index("plan['artifact_policy']");prep=prep[:at]+extra+prep[at:]
(ROOT/'prepare.py').write_bytes(prep.encode())
print({'same10_statements':True,'repair':'explicit empty existential elimination after reducing wrong-width conditional','both_failed_original_histories_retained':True,'guards_unchanged':True})
