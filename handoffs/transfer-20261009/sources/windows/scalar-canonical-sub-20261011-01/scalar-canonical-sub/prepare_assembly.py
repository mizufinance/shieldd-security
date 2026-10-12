from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-canonical-add-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-canonical-add-20261011-02'","CURRENT = DIAG / 'transfer-scalar-canonical-sub-20261011-02'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-canonical-add-checkpoint-20261011-02'","CHECKPOINT = DIAG / 'transfer-scalar-canonical-sub-checkpoint-20261011-02'"),
 ("MODULE = 'TransferScalarCanonicalAdd01'","MODULE = 'TransferScalarCanonicalSub01'"),
 ("manager_endpoint = DIAG / 'transfer-checked-word-accepted-input-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-scalar-canonical-add-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-checked-word-accepted-input-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-canonical-add-endpoint01.tar.xz'"),
 ('af2ecc156b39c86f61342b519d3b2e5e914ee91d27ba3d9a27966d89f2179d86','fe28cc465a19ec8d669958ab3127368cd15585d8a5c1c88dc303dc5204d6ebd8'),
 ("'module': 'TransferCheckedWordAcceptedInput01'","'module': 'TransferScalarCanonicalAdd01'"),
 ("reference = {'checked_word_accepted_input':","reference = {'scalar_canonical_add':"),
 ("assert len(fresh) == 5","assert len(fresh) == 3"),
 ("assert len(manager_reports) == 4","assert len(manager_reports) == 5"),
 ("manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-5-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 2"),
 ("archive = ROOT / 'portable-windows-scalar-canonical-add-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-canonical-sub-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-5-complete-declarations.txt'","add(stdout, 'reports/fresh-3-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 144','== 145').replace('== 1167','== 1172').replace('one-hundred-forty-four-module','one-hundred-forty-five-module').replace('1167 original inherited complete reports','1172 original inherited complete reports').replace('verified 1167 inherited reports','verified 1172 inherited reports')
start=s.index("failed=DIAG/'transfer-scalar-canonical-add-20261011-01'");end=s.index("row=mapping['scalar_canonical_add_source_shape']",start)
s=s[:start]+"""failed=DIAG/'transfer-scalar-canonical-sub-20261011-01'
for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarCanonicalSub01.lean','project/ShielddSecurity/TransferScalarCanonicalSub01.lean','runs/01-TransferScalarCanonicalSub01/stdout.txt','context/scalar-canonical-sub-shape.json']:
    row=pin(failed/name)
    assert row in plan['pins']
    add(failed/name,'rejected-canonical-sub-attempt01/'+name,'original let-binding and Boolean-if proof errors, full placeholder reports; entire attempt zero credit, not a negative control')
row=mapping['scalar_canonical_sub_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-canonical-sub-shape.json','exact authenticated cached four SBB/four masked ADC source body; static identity only, Rust/compiler/caller correspondence separate')
"""+s[end:]
s=s.replace('transfer-scalar-canonical-add-endpoint-v1','transfer-scalar-canonical-sub-endpoint-v1').replace('SCALAR_FOUR_ADC_THEN_MODULUS_SUB_CANONICAL_PRESERVATION_QUALIFIED','SCALAR_FOUR_SBB_THEN_MASKED_ADC_CANONICAL_SUBTRACTION_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Three complete audits, one definition/two theorems. Source four SBB/borrow-masked actual ADC retains four limbs and canonical exact modular subtraction; underflow derived from actual operands and borrow recurrence. Original proof failure retained11 raw artifacts zero credit; expose let binding and explicit Boolean-if proof repairs only, definitions/contracts/guards unchanged. Private Scalar global invariant/all other operations/native Rust/compiler/caller/full Transfer OPEN; no ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-canonical-sub-checkpoint-20261011-02';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-canonical-add-checkpoint-20261011-02/preservation_check.py').read_bytes())
print({'fresh_reports':3,'inherited_reports':1172,'owned_modules':145})
