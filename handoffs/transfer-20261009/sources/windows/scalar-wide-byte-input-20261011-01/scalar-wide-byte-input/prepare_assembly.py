from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-wide-constructor-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-scalar-wide-constructor-20261011-03'","CURRENT = DIAG / 'transfer-scalar-wide-byte-input-20261011-02'"),
 ("CHECKPOINT = DIAG / 'transfer-scalar-wide-constructor-checkpoint-20261011-03'","CHECKPOINT = DIAG / 'transfer-scalar-wide-byte-input-checkpoint-20261011-02'"),
 ("MODULE = 'TransferScalarWideConstructor01'","MODULE = 'TransferScalarWideByteInput01'"),
 ("manager_endpoint = DIAG / 'transfer-scalar-program-invariant-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-scalar-wide-constructor-endpoint-20261011-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-scalar-program-invariant-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-wide-constructor-endpoint01.tar.xz'"),
 ('9c3be4a7fd1e7e2af8aa06c7836a8dbb10d7dbcd2a1ccf77fa956c484c42b42b','9ee3d0e23a336975ec7be81a7627090b4e5c7530167a89f6a02a5bfd17e83881'),
 ("'module': 'TransferScalarProgramInvariant01'","'module': 'TransferScalarWideConstructor01'"),
 ("reference = {'scalar_program_invariant':","reference = {'scalar_wide_constructor':"),
 ("assert len(fresh) == 6","assert len(fresh) == 4"),
 ("assert len(manager_reports) == 4","assert len(manager_reports) == 6"),
 ("manager_stdout = tar.extractfile('reports/fresh-4-complete-declarations.txt')","manager_stdout = tar.extractfile('reports/fresh-6-complete-declarations.txt')"),
 ("assert declaration_kinds.count('def') == 3 and declaration_kinds.count('theorem') == 3","assert declaration_kinds.count('def') == 2 and declaration_kinds.count('theorem') == 2"),
 ("archive = ROOT / 'portable-windows-scalar-wide-constructor-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-wide-byte-input-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-6-complete-declarations.txt'","add(stdout, 'reports/fresh-4-complete-declarations.txt'")]:replace(a,b)
s=s.replace('== 148','== 149').replace('== 1185','== 1191').replace('one-hundred-forty-eight-module','one-hundred-forty-nine-module').replace('1185 original inherited complete reports','1191 original inherited complete reports').replace('verified 1185 inherited reports','verified 1191 inherited reports')
start=s.index('for attempt in [1,2]:');end=s.index("row=mapping['scalar_wide_constructor_source_shape']",start)
s=s[:start]+"""failed=DIAG/'transfer-scalar-wide-byte-input-20261011-01'
for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarWideByteInput01.lean','project/ShielddSecurity/TransferScalarWideByteInput01.lean','runs/01-TransferScalarWideByteInput01/stdout.txt','context/scalar-wide-byte-input-shape.json']:
    row=pin(failed/name)
    assert row in plan['pins']
    add(failed/name,'rejected-wide-byte-input-attempt01/'+name,'original extra rfl after closed length proof, full placeholder reports retained; entire attempt zero credit, not a negative control')
row=mapping['scalar_wide_byte_input_source_shape']
assert pin(row['path'])==row and row in plan['pins']
add(row['path'],'context/scalar-wide-byte-input-shape.json','exact authenticated cached eight ordered8-byte LE source slices/from_u512 call; static identity only, native slice/array/primitive/compiler/caller correspondence separate')
"""+s[end:]
s=s.replace("'rejected_attempts': 2","'rejected_attempts': 1").replace('transfer-scalar-wide-constructor-endpoint-v1','transfer-scalar-wide-byte-input-endpoint-v1').replace('ARBITRARY_WIDE_DIGITS_SOURCE_CONSTRUCTOR_CANONICAL_EXACT_KEY_QUALIFIED','ARBITRARY_64_SOURCE_BYTES_CONSTRUCTOR_CANONICAL_EXACT_KEY_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Four complete audits, two definitions/two theorems. Original64-byte input derives exact eight LE word reads, low/high digit integer reconstruction and canonical complete wide constructor payload/key/32-byte serialization. No caller desired digits/input canonical bounds/payload/key. Original proof error retained11 raw artifacts zero credit; remove extra rfl after closed length rewrite only, definitions/contracts/guards unchanged. Native slice/array/index/library/private Scalar/primitive/compiler/caller/full Transfer OPEN; no ancestors replayed.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
checkpoint=DIAG/'transfer-scalar-wide-byte-input-checkpoint-20261011-02';checkpoint.mkdir()
(checkpoint/'preservation_check.py').write_bytes((DIAG/'transfer-scalar-wide-constructor-checkpoint-20261011-03/preservation_check.py').read_bytes())
print({'fresh_reports':4,'inherited_reports':1191,'owned_modules':149})
