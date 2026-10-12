from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-program-invariant-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-program-invariant-20261011-01'","CURRENT = DIAG / 'transfer-scalar-wide-constructor-20261011-03'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-program-invariant-checkpoint-20261011-01'","CHECKPOINT = DIAG / 'transfer-scalar-wide-constructor-checkpoint-20261011-03'"),
 ("MODULE = 'TransferScalarProgramInvariant01'","MODULE = 'TransferScalarWideConstructor01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-canonical-neg-endpoint-20261011-03'","manager_endpoint = DIAG / 'transfer-scalar-program-invariant-endpoint-20261011-01'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-canonical-neg-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-program-invariant-endpoint01.tar.xz'"),
 ('bb36156065a655239e4c17d7dca430ac2d4ae2e39c8753b2884eaac189428ec8','9c3be4a7fd1e7e2af8aa06c7836a8dbb10d7dbcd2a1ccf77fa956c484c42b42b'),
 ("'module': 'TransferScalarCanonicalNeg01'","'module': 'TransferScalarProgramInvariant01'"),
 ("reference = {'scalar_canonical_neg':","reference = {'scalar_program_invariant':"),
 ("assert len(fresh) == 4","assert len(fresh) == 6"),
 ("assert len(manager_reports) == 6","assert len(manager_reports) == 4"),
 ("manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 2 and declaration_kinds.count('inductive') == 1 and declaration_kinds.count('theorem') == 1","assert declaration_kinds.count('def') == 3 and declaration_kinds.count('theorem') == 3"),
 ("archive = ROOT / 'portable-windows-scalar-program-invariant-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-wide-constructor-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-4-complete-declarations.txt'","add(stdout, 'reports/fresh-6-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 147','== 148').replace('== 1181','== 1185').replace('one-hundred-forty-seven-module','one-hundred-forty-eight-module').replace('1181 original inherited complete reports','1185 original inherited complete reports').replace('verified 1181 inherited reports','verified 1185 inherited reports')
at=s.index("row=mapping['scalar_program_family_source_shape']")
extra="""for attempt in [1,2]:
    failed=DIAG/('transfer-scalar-wide-constructor-20261011-0'+str(attempt))
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarWideConstructor01.lean','project/ShielddSecurity/TransferScalarWideConstructor01.lean','context/scalar-wide-constructor-shape.json']
    if attempt==2:
        names.append('runs/01-TransferScalarWideConstructor01/stdout.txt')
    else:
        assert not (failed/'runs/01-TransferScalarWideConstructor01/stdout.txt').exists()
    for name in names:
        row=pin(failed/name)
        assert row in plan['pins']
        add(failed/name,'rejected-wide-constructor-attempt0'+str(attempt)+'/'+name,'original pre-Lean physical pressure or finite recursion congruence proof failure; full history retained, entire attempt zero credit, not a negative control')
row=mapping['scalar_wide_constructor_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-wide-constructor-shape.json','exact authenticated cached R3 literal/eight word low-high split/two mul R2/R3 then add source body; static identity only, Rust/compiler/caller correspondence separate')
"""
s=s[:at]+extra+s[at:]
s=s.replace("'rejected_attempts': 0","'rejected_attempts': 2").replace('transfer-scalar-program-invariant-endpoint-v1','transfer-scalar-wide-constructor-endpoint-v1').replace('REPRESENTED_SCALAR_RAW_OPERATION_FAMILY_DERIVES_CANONICAL_INVARIANT_QUALIFIED','ARBITRARY_WIDE_DIGITS_SOURCE_CONSTRUCTOR_CANONICAL_EXACT_KEY_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete audits, three definitions/three theorems. Pinned R3 literal/range/inverse derives high-digit actual modeled multiplication canonical Montgomery value. Low R2/high R3 products and actual ADC/sub add derive canonical wide payload and exact complete512-bit integer key, no input canonical premise. Original pre-Lean pressure and recursion proof failure retained21 raw artifacts zero credit; explicit modulo congrArg repair only, definitions/contracts/guards unchanged. Native bytes/eight-index/private Scalar/primitive/compiler/caller/full Transfer OPEN; no ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-wide-constructor-checkpoint-20261011-03';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-program-invariant-checkpoint-20261011-01/preservation_check.py').read_bytes())
print({'fresh_reports':6,'inherited_reports':1185,'owned_modules':148})
