from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent;old=DIAG/'transfer-scalar-additive-field-20261012-01'
assert not (ROOT/'prepare.py').exists()
source=(old/'handwritten/TransferScalarAdditiveField01.lean').read_text()
before='    (left right output : Nat) (leftRange : left < nullifierModulus)\n    (rightRange : right < nullifierModulus) (outputRange : output < nullifierModulus)'
assert source.count(before)==1
source=source.replace(before,'    (left right output : Nat)\n    (rightRange : right < nullifierModulus) (outputRange : output < nullifierModulus)')
before='    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) scaled'
assert source.count(before)==1;source=source.replace(before,'    (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) scaled')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarAdditiveField01.lean').write_bytes(source.encode())
(ROOT/'prepare_recipe.py').write_bytes((old/'prepare_recipe.py').read_bytes())
prep=(old/'prepare.py').read_text().replace("POOL=DIAG/'transfer-scalar-additive-field-owned-floor-20261012-01'","POOL=DIAG/'transfer-scalar-additive-field-owned-floor-20261012-02'")
extra="""failed=DIAG/'transfer-scalar-additive-field-20261012-01'
assert json.loads((failed/'events.jsonl').read_text().splitlines()[-1])['result']['status']=='failed'
plan['pins'] += [pin(p) for p in sorted(failed.rglob('*')) if p.is_file()]+[pin(ROOT/'prepare_from01.py')]
"""
at=prep.index("plan['artifact_policy']");prep=prep[:at]+extra+prep[at:]
(ROOT/'prepare.py').write_bytes(prep.encode())
print({'strengthened_generic_lemma':'remove unused left-residue bound; relation and output/right bounds already suffice','all_other7_statements_unchanged':True,'original_warning_and_object_retained':True,'all_guards_unchanged':True})
