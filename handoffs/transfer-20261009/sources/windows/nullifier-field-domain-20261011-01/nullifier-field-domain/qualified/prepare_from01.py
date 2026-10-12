from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent;old=DIAG/'transfer-nullifier-field-domain-20261012-01'
assert not (ROOT/'prepare.py').exists()
source=(old/'handwritten/TransferNullifierFieldDomain01.lean').read_text()
assert source.count('value.isLt.trans (by decide : nullifierModulus < 256 ^ 32)')==1
source=source.replace('value.isLt.trans (by decide : nullifierModulus < 256 ^ 32)','Nat.lt_trans value.isLt (by decide : nullifierModulus < 256 ^ 32)')
before='    (sourceFieldResidue scalar).val = montgomeryValue scalar.words := by\n  exact '
assert source.count(before)==1;source=source.replace(before,'    (sourceFieldResidue scalar).val = montgomeryValue scalar.words := by\n  dsimp only [sourceFieldResidue]\n  exact ')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferNullifierFieldDomain01.lean').write_bytes(source.encode())
(ROOT/'prepare_recipe.py').write_bytes((old/'prepare_recipe.py').read_bytes())
prep=(old/'prepare.py').read_text().replace("POOL=DIAG/'transfer-nullifier-field-domain-owned-floor-20261012-01'","POOL=DIAG/'transfer-nullifier-field-domain-owned-floor-20261012-02'")
extra="""failed=DIAG/'transfer-nullifier-field-domain-20261012-01'
assert json.loads((failed/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
plan['pins'] += [pin(p) for p in sorted(failed.rglob('*')) if p.is_file()]+[pin(ROOT/'prepare_from01.py')]
"""
at=prep.index("plan['artifact_policy']");prep=prep[:at]+extra+prep[at:]
(ROOT/'prepare.py').write_bytes(prep.encode())
print({'same11_statements':True,'repair':'explicit Nat.lt_trans; reduce only sourceFieldResidue before serializer theorem application','original_failed_module_and_reports_retained':True,'finite_heartbeat_and_all_guards_unchanged':True})
