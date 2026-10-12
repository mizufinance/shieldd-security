from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-canonical-sub-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-canonical-sub-20261011-02'","CURRENT = DIAG / 'transfer-scalar-canonical-neg-20261011-03'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-canonical-sub-checkpoint-20261011-02'","CHECKPOINT = DIAG / 'transfer-scalar-canonical-neg-checkpoint-20261011-03'"),
 ("MODULE = 'TransferScalarCanonicalSub01'","MODULE = 'TransferScalarCanonicalNeg01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-canonical-add-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-scalar-canonical-sub-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-canonical-add-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-canonical-sub-endpoint01.tar.xz'"),
 ('fe28cc465a19ec8d669958ab3127368cd15585d8a5c1c88dc303dc5204d6ebd8','ca22dd77fd5bbebed349c11058f4d4d998e79e94042bdf29a7ee7a8fbb099f5d'),
 ("'module': 'TransferScalarCanonicalAdd01'","'module': 'TransferScalarCanonicalSub01'"),
 ("reference = {'scalar_canonical_add':","reference = {'scalar_canonical_sub':"),
 ("assert len(fresh) == 3","assert len(fresh) == 6"),
 ("assert len(manager_reports) == 5","assert len(manager_reports) == 3"),
 ("manager_stdout = tar.extractfile('reports/fresh-5-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-3-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 1 and declaration_kinds.count('theorem') == 2","assert declaration_kinds.count('def') == 3 and declaration_kinds.count('theorem') == 3"),
 ("archive = ROOT / 'portable-windows-scalar-canonical-sub-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-canonical-neg-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-3-complete-declarations.txt'","add(stdout, 'reports/fresh-6-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 145','== 146').replace('== 1172','== 1175').replace('one-hundred-forty-five-module','one-hundred-forty-six-module').replace('1172 original inherited complete reports','1175 original inherited complete reports').replace('verified 1172 inherited reports','verified 1175 inherited reports')
start=s.index("failed=DIAG/'transfer-scalar-canonical-sub-20261011-01'");end=s.index("row=mapping['scalar_canonical_sub_source_shape']",start)
s=s[:start]+"""for attempt in [1,2]:
    failed=DIAG/('transfer-scalar-canonical-neg-20261011-0'+str(attempt))
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarCanonicalNeg01.lean','project/ShielddSecurity/TransferScalarCanonicalNeg01.lean','context/scalar-canonical-neg-shape.json']
    if attempt==1:
        names.append('runs/01-TransferScalarCanonicalNeg01/stdout.txt')
    else:
        assert not (failed/'runs/01-TransferScalarCanonicalNeg01/stdout.txt').exists()
    for name in names:
        row=pin(failed/name)
        assert row in plan['pins']
        add(failed/name,'rejected-canonical-neg-attempt0'+str(attempt)+'/'+name,'original zero-summand proof error or pre-Lean physical pressure, full original history; entire attempt zero credit, not a negative control')
row=mapping['scalar_canonical_neg_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-canonical-neg-shape.json','exact authenticated cached four SBB/MODULUS-self OR-zero wrapping-subtract mask source body; static identity only, Rust/compiler/caller correspondence separate')
"""+s[end:]
s=s.replace("'rejected_attempts': 1","'rejected_attempts': 2").replace('transfer-scalar-canonical-sub-endpoint-v1','transfer-scalar-canonical-neg-endpoint-v1').replace('SCALAR_FOUR_SBB_THEN_MASKED_ADC_CANONICAL_SUBTRACTION_QUALIFIED','SCALAR_FOUR_SBB_AND_NONZERO_MASK_CANONICAL_NEGATION_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete audits, three definitions/three theorems. Symbolic OR walk detects exact raw zero; Boolean cast/wrapping subtraction selects zero/all-ones mask. Canonical operand derives no ignored borrow in actual MODULUS-self four SBB recurrence and four canonical output limbs with exact modular negation, including zero. Original proof failure and pre-Lean pressure retained21 raw artifacts zero credit; explicit summand/product type repair only, definitions/contracts/guards unchanged. Private Scalar global invariant/all other operations/native Rust/compiler/caller/full Transfer OPEN; no ancestors replayed. Assembly verifies every source and object identity with memoized source-only archive reads; no checks or evidence replay skipped.'}"+s[end:]
# Read each original archive once while retaining its exact hash and every source comparison.
at=s.index("for selected in pool['selected']:")
helper="""archive_source_cache={}
def original_lean_sources(carrier):
    key=carrier['path']
    if key not in archive_source_cache:
        assert pin(key)==carrier
        with tarfile.open(key,'r:xz') as tar:
            archive_source_cache[key]={name:tar.extractfile(name).read() for name in tar.getnames()
                if name.startswith('source/ShielddSecurity/') and name.endswith('.lean')}
    return archive_source_cache[key]
"""
s=s[:at]+helper+s[at:]
old="""        assert pin(carrier['path']) == carrier
        with tarfile.open(carrier['path'], 'r:xz') as tar:
            if member in tar.getnames():
                assert tar.extractfile(member).read() == Path(selected['source']['path']).read_bytes()
                found = True
                break
"""
new="""        originals=original_lean_sources(carrier)
        if member in originals:
            assert originals[member] == Path(selected['source']['path']).read_bytes()
            found = True
            break
"""
replace(old,new)
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-canonical-neg-checkpoint-20261011-03';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-canonical-sub-checkpoint-20261011-02/preservation_check.py').read_bytes())
print({'fresh_reports':6,'inherited_reports':1175,'owned_modules':146,'source_archive_read_memoization_only':True})
