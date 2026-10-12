from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-checked-word-accepted-input-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-checked-word-accepted-input-20261011-02'","CURRENT = DIAG / 'transfer-scalar-canonical-add-20261011-02'"),
 ("CHECKPOINT = DIAG / 'transfer-checked-word-accepted-input-checkpoint-20261011-02'","CHECKPOINT = DIAG / 'transfer-scalar-canonical-add-checkpoint-20261011-02'"),
 ("MODULE = 'TransferCheckedWordAcceptedInput01'","MODULE = 'TransferScalarCanonicalAdd01'"),
 ("manager_endpoint = DIAG / 'transfer-checked-word-fresh-snapshot-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-checked-word-accepted-input-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-checked-word-fresh-snapshot-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-checked-word-accepted-input-endpoint01.tar.xz'"),
 ('b2f49a56b38d065e140f368d388ce861bc363508bb9ff663e9b7e192b919228f','af2ecc156b39c86f61342b519d3b2e5e914ee91d27ba3d9a27966d89f2179d86'),
 ("'module': 'TransferCheckedWordFreshSnapshot01'","'module': 'TransferCheckedWordAcceptedInput01'"),
 ("reference = {'checked_word_fresh_snapshot':","reference = {'checked_word_accepted_input':"),
 ("assert len(fresh) == 4","assert len(fresh) == 5"),
 ("assert len(manager_reports) == 5","assert len(manager_reports) == 4"),
 ("manager_stdout = tar.extractfile('reports/fresh-5-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 3"),
 ("archive = ROOT / 'portable-windows-checked-word-accepted-input-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-canonical-add-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-4-complete-declarations.txt'","add(stdout, 'reports/fresh-5-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 143','== 144').replace('== 1163','== 1167').replace('one-hundred-forty-three-module','one-hundred-forty-four-module').replace('1163 original inherited complete reports','1167 original inherited complete reports').replace('verified 1163 inherited reports','verified 1167 inherited reports')
start=s.index("failed=DIAG/'transfer-checked-word-accepted-input-20261011-01'");end=s.index("row=mapping['checked_word_accepted_source_shape']",start)
s=s[:start]+"""failed=DIAG/'transfer-scalar-canonical-add-20261011-01'
for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarCanonicalAdd01.lean','project/ShielddSecurity/TransferScalarCanonicalAdd01.lean','runs/01-TransferScalarCanonicalAdd01/stdout.txt','context/scalar-canonical-add-shape.json']:
    row=pin(failed/name)
    assert row in plan['pins']
    add(failed/name,'rejected-canonical-add-attempt01/'+name,'original three proof gaps and full placeholder reports; entire attempt zero credit, not a negative control')
row=mapping['scalar_canonical_add_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-canonical-add-shape.json','exact authenticated cached four ADC/sub-modulus source body; static identity only, Rust/compiler/caller correspondence separate')
"""+s[end:]
s=s.replace('transfer-checked-word-accepted-input-endpoint-v1','transfer-scalar-canonical-add-endpoint-v1').replace('ACTUAL_FRESH_CHECKED_WORD_GETTER_DERIVES_EXACT_ACCEPTED_CANONICAL_KEY_VECTOR_QUALIFIED','SCALAR_FOUR_ADC_THEN_MODULUS_SUB_CANONICAL_PRESERVATION_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Five complete audits, two definitions/three theorems. Symbolic actual ADC walk equals proved unit MAC walk. Canonical operands derive four limbs, zero discarded carry and exact integer sum; source-shaped modulus sub/masked ADC yields canonical exact modular sum. Original proof failure retained11 raw artifacts zero credit; reflexive length and subtraction simplification repairs only, definitions/contracts/guards unchanged. Private Scalar global invariant/all other operations/native Rust/compiler/caller/full Transfer OPEN; no ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-canonical-add-checkpoint-20261011-02';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-checked-word-accepted-input-checkpoint-20261011-02/preservation_check.py').read_bytes())
print({'fresh_reports':5,'inherited_reports':1167,'owned_modules':144})
