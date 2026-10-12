from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-input-family-endpoint-20261011-04/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-input-family-20261011-04'","CURRENT = DIAG / 'transfer-scalar-square-cross-20261011-02'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-input-family-checkpoint-20261011-04'","CHECKPOINT = DIAG / 'transfer-scalar-square-cross-checkpoint-20261011-02'"),
 ("MODULE = 'TransferScalarInputFamily01'","MODULE = 'TransferScalarSquareCross01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-wide-byte-input-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-scalar-input-family-endpoint-20261011-04'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-wide-byte-input-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-input-family-endpoint01.tar.xz'"),
 ('9cb2746a40c5281043b725eadcd9c458cde6e3c8253770cf4519846ec23b2dff','1fd09e6666ffe57133f74f181777e702e48d92f0a5ecf529b6535c93bcb2a6a5'),
 ("'module': 'TransferScalarWideByteInput01'","'module': 'TransferScalarInputFamily01'"),
 ("reference = {'scalar_wide_byte_input':","reference = {'scalar_input_family':"),
 ("assert len(fresh) == 5","assert len(fresh) == 6"),
 ("assert len(manager_reports) == 4","assert len(manager_reports) == 5"),
 ("manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-5-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 1 and declaration_kinds.count('inductive') == 1 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('def') == 3 and declaration_kinds.count('theorem') == 3"),
 ("archive = ROOT / 'portable-windows-scalar-input-family-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-square-cross-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-5-complete-declarations.txt'","add(stdout, 'reports/fresh-6-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 150','== 151').replace('== 1195','== 1200').replace('one-hundred-fifty-module','one-hundred-fifty-one-module').replace('1195 original inherited complete reports','1200 original inherited complete reports').replace('verified 1195 inherited reports','verified 1200 inherited reports')
start=s.index('for attempt in [1,2,3]:');end=s.index("row=mapping['scalar_input_family_source_shape']",start)
s=s[:start]+"""failed=DIAG/'transfer-scalar-square-cross-20261011-01'
for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/scalar-square-cross-shape.json','handwritten/TransferScalarSquareCross01.lean','project/ShielddSecurity/TransferScalarSquareCross01.lean','runs/01-TransferScalarSquareCross01/stdout.txt']:
    row=pin(failed/name)
    assert row in plan['pins']
    add(failed/name,'prior-square-cross-attempt01/'+name,'original Lean proof failure;11 raw artifacts, zero credit, not negative control')
row=mapping['scalar_square_cross_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-square-cross-shape.json','exact authenticated cached six shrinking MAC row source and remaining square body; static association only')
"""+s[end:]
s=s.replace("'rejected_attempts': 2, 'withdrawn_unrun_sources': 1","'rejected_attempts': 1, 'withdrawn_unrun_sources': 0").replace('transfer-scalar-input-family-endpoint-v1','transfer-scalar-square-cross-endpoint-v1').replace('EXTENDED_SCALAR_RAW_WIDE_CANONICAL_BYTES_FAMILY_INVARIANT_QUALIFIED','SOURCE_SIX_MAC_SQUARE_CROSS_PREFIX_EXACT_INTEGER_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete declarations:three definitions/three theorems. Original11 raw proof failure artifacts retained zero credit; singleton conjunction, intended outer recurrence and final conjunction proof-only repairs. Source definitions/contracts/finite guards unchanged; no ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-square-cross-checkpoint-20261011-02';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-input-family-checkpoint-20261011-04/preservation_check.py').read_bytes())
print({'fresh_reports':6,'inherited_reports':1200,'owned_modules':151})
