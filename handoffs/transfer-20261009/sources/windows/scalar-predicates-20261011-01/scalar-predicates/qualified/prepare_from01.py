from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent;old=DIAG/'transfer-scalar-predicates-20261012-01'
assert not (ROOT/'prepare.py').exists()
source=(old/'handwritten/TransferScalarPredicates01.lean').read_text()
before='      rw [Nat.zero_mul]\n      rfl';assert source.count(before)==1
source=source.replace(before,'      rw [Nat.zero_mul]')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarPredicates01.lean').write_bytes(source.encode())
(ROOT/'prepare_recipe.py').write_bytes((old/'prepare_recipe.py').read_bytes())
prep=(old/'prepare.py').read_text().replace("POOL=DIAG/'transfer-scalar-predicates-owned-floor-20261012-01'","POOL=DIAG/'transfer-scalar-predicates-owned-floor-20261012-02'")
extra="""failed=DIAG/'transfer-scalar-predicates-20261012-01'
assert json.loads((failed/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
plan['pins'] += [pin(p) for p in sorted(failed.rglob('*')) if p.is_file()]+[pin(ROOT/'prepare_from01.py')]
"""
at=prep.index("plan['artifact_policy']");prep=prep[:at]+extra+prep[at:]
(ROOT/'prepare.py').write_bytes(prep.encode())
print({'same13_statements':True,'repair':'remove redundant rfl after zero-product rewrite closes the goal','original_raw_failure_retained':True,'all_guards_unchanged':True})
