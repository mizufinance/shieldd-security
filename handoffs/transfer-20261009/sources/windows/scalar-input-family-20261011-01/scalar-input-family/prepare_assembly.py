from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-wide-byte-input-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-wide-byte-input-20261011-02'","CURRENT = DIAG / 'transfer-scalar-input-family-20261011-04'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-wide-byte-input-checkpoint-20261011-02'","CHECKPOINT = DIAG / 'transfer-scalar-input-family-checkpoint-20261011-04'"),
 ("MODULE = 'TransferScalarWideByteInput01'","MODULE = 'TransferScalarInputFamily01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-wide-constructor-endpoint-20261011-03'","manager_endpoint = DIAG / 'transfer-scalar-wide-byte-input-endpoint-20261011-02'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-wide-constructor-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-wide-byte-input-endpoint01.tar.xz'"),
 ('9ee3d0e23a336975ec7be81a7627090b4e5c7530167a89f6a02a5bfd17e83881','9cb2746a40c5281043b725eadcd9c458cde6e3c8253770cf4519846ec23b2dff'),
 ("'module': 'TransferScalarWideConstructor01'","'module': 'TransferScalarWideByteInput01'"),
 ("reference = {'scalar_wide_constructor':","reference = {'scalar_wide_byte_input':"),
 ("assert len(fresh) == 4","assert len(fresh) == 5"),
 ("assert len(manager_reports) == 6","assert len(manager_reports) == 4"),
 ("manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 2","assert declaration_kinds.count('def') == 1 and declaration_kinds.count('inductive') == 1 and declaration_kinds.count('theorem') == 3"),
 ("archive = ROOT / 'portable-windows-scalar-wide-byte-input-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-input-family-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-4-complete-declarations.txt'","add(stdout, 'reports/fresh-5-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 149','== 150').replace('== 1191','== 1195').replace('one-hundred-forty-nine-module','one-hundred-fifty-module').replace('1191 original inherited complete reports','1195 original inherited complete reports').replace('verified 1191 inherited reports','verified 1195 inherited reports')
start=s.index("failed=DIAG/'transfer-scalar-wide-byte-input-20261011-01'");end=s.index("row=mapping['scalar_wide_byte_input_source_shape']",start)
s=s[:start]+"""for attempt in [1,2,3]:
    failed=DIAG/('transfer-scalar-input-family-20261011-0'+str(attempt))
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','handwritten/TransferScalarInputFamily01.lean','project/ShielddSecurity/TransferScalarInputFamily01.lean','context/scalar-input-family-shape.json']
    if attempt>1:
        names.append('events.jsonl')
    else:
        assert not (failed/'events.jsonl').exists()
    if attempt==3:
        names.append('runs/01-TransferScalarInputFamily01/stdout.txt')
    else:
        assert not (failed/'runs/01-TransferScalarInputFamily01/stdout.txt').exists()
    for name in names:
        row=pin(failed/name)
        assert row in plan['pins']
        add(failed/name,'prior-input-family-attempt0'+str(attempt)+'/'+name,'original withdrawn unrun preflight source, pre-Lean physical pressure, or beta-projection proof failure; exact30 raw artifacts total, entire prior sources zero credit, not negative controls')
row=mapping['scalar_input_family_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-input-family-shape.json','exact authenticated cached32-byte Choice/CtOption/R2 source body and explicit represented/excluded family inventory; static association only, native binding separate')
"""+s[end:]
s=s.replace("'rejected_attempts': 1","'rejected_attempts': 2, 'withdrawn_unrun_sources': 1").replace('transfer-scalar-wide-byte-input-endpoint-v1','transfer-scalar-input-family-endpoint-v1').replace('ARBITRARY_64_SOURCE_BYTES_CONSTRUCTOR_CANONICAL_EXACT_KEY_QUALIFIED','EXTENDED_SCALAR_RAW_WIDE_CANONICAL_BYTES_FAMILY_INVARIANT_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Five complete audits, one inductive/one definition/three theorems. Exact modeled32-byte Choice success/refusal projection and original-byte reserialization retained. Extended raw/wide/bytes operation family derives canonical output fields and exact32-byte Montgomery keys without caller operand bound; constructor refusal propagates. Withdrawn unrun preflight9, pressure10, beta-projection failure11 original raw artifacts retained zero credit; conditional finishing tactic and beta reduction proof-only repairs, definitions/contracts/guards unchanged. Square/pow/invert/random/private constructors/native library/Choice/CtOption/program/compiler/caller/full Transfer OPEN; no ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-input-family-checkpoint-20261011-04';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-wide-byte-input-checkpoint-20261011-02/preservation_check.py').read_bytes())
print({'fresh_reports':5,'inherited_reports':1195,'owned_modules':150})
