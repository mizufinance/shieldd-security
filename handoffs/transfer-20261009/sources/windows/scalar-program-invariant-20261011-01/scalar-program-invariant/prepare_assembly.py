from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-canonical-neg-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-canonical-neg-20261011-03'","CURRENT = DIAG / 'transfer-scalar-program-invariant-20261011-01'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-canonical-neg-checkpoint-20261011-03'","CHECKPOINT = DIAG / 'transfer-scalar-program-invariant-checkpoint-20261011-01'"),
 ("MODULE = 'TransferScalarCanonicalNeg01'","MODULE = 'TransferScalarProgramInvariant01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-canonical-sub-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-scalar-canonical-neg-endpoint-20261011-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-canonical-sub-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-canonical-neg-endpoint01.tar.xz'"),
 ('ca22dd77fd5bbebed349c11058f4d4d998e79e94042bdf29a7ee7a8fbb099f5d','bb36156065a655239e4c17d7dca430ac2d4ae2e39c8753b2884eaac189428ec8'),
 ("'module': 'TransferScalarCanonicalSub01'","'module': 'TransferScalarCanonicalNeg01'"),
 ("reference = {'scalar_canonical_sub':","reference = {'scalar_canonical_neg':"),
 ("assert len(fresh) == 6","assert len(fresh) == 4"),
 ("assert len(manager_reports) == 3","assert len(manager_reports) == 6"),
 ("manager_stdout = tar.extractfile('reports/fresh-3-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 3 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('def') == 2 and declaration_kinds.count('inductive') == 1 and declaration_kinds.count('theorem') == 1"),
 ("archive = ROOT / 'portable-windows-scalar-canonical-neg-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-program-invariant-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-6-complete-declarations.txt'","add(stdout, 'reports/fresh-4-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 146','== 147').replace('== 1175','== 1181').replace('one-hundred-forty-six-module','one-hundred-forty-seven-module').replace('1175 original inherited complete reports','1181 original inherited complete reports').replace('verified 1175 inherited reports','verified 1181 inherited reports')
start=s.index('for attempt in [1,2]:');end=s.index("row=mapping['scalar_canonical_neg_source_shape']",start)
s=s[:start]+"""row=mapping['scalar_program_family_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-program-family-shape.json','exact authenticated cached from_raw/R2 and add/sub/mul/neg/double bodies; static association only, native family/caller/compiler binding separate')
"""+s[end:]
s=s.replace("'rejected_attempts': 2","'rejected_attempts': 0").replace('transfer-scalar-canonical-neg-endpoint-v1','transfer-scalar-program-invariant-endpoint-v1').replace('SCALAR_FOUR_SBB_AND_NONZERO_MASK_CANONICAL_NEGATION_QUALIFIED','REPRESENTED_SCALAR_RAW_OPERATION_FAMILY_DERIVES_CANONICAL_INVARIANT_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Four complete audits, one inductive/two definitions/one theorem. Actual eval terms construct every output from exact prior proved operation widths and bounds, starting from arbitrary raw words through R2 conversion. Canonical raw bound and exact32 byte Montgomery key derived without caller operand invariant. Represented family only; no assertion every native Scalar originates here, excluded square/pow/invert/from-wide/random/private constructors remain OPEN. First attempt passes; no ancestor replay/native credit; complete original histories retained in exact ancestry.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-program-invariant-checkpoint-20261011-01';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-canonical-neg-checkpoint-20261011-03/preservation_check.py').read_bytes())
print({'fresh_reports':4,'inherited_reports':1181,'owned_modules':147})
