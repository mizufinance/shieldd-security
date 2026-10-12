from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent;old=DIAG/'transfer-scalar-input-semantics-20261012-01'
assert not (ROOT/'prepare.py').exists()
source=(old/'handwritten/TransferScalarInputSemantics01.lean').read_text()
assert source.count('fun scalar => montgomeryValue scalar.words')==16
source=source.replace('fun scalar => montgomeryValue scalar.words','fun scalar : CanonicalScalar => montgomeryValue scalar.words')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarInputSemantics01.lean').write_bytes(source.encode())
(ROOT/'prepare_recipe.py').write_bytes((old/'prepare_recipe.py').read_bytes())
prep=(old/'prepare.py').read_text().replace("POOL=DIAG/'transfer-scalar-input-semantics-owned-floor-20261012-01'","POOL=DIAG/'transfer-scalar-input-semantics-owned-floor-20261012-02'")
extra="""failed=DIAG/'transfer-scalar-input-semantics-20261012-01'
assert json.loads((failed/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
plan['pins'] += [pin(p) for p in sorted(failed.rglob('*')) if p.is_file()]+[pin(ROOT/'prepare_from01.py')]
"""
at=prep.index("plan['artifact_policy']");prep=prep[:at]+extra+prep[at:]
(ROOT/'prepare.py').write_bytes(prep.encode())
print({'same7_intended_statements':True,'repair':'explicit CanonicalScalar lambda domains for Option/do elaboration','original_invalid-field_reports_retained':True,'finite_guards_unchanged':True})
