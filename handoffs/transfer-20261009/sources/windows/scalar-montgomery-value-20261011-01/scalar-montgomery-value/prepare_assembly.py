"""Seal exact finite Montgomery value with both immutable failed proof attempts."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-little-endian-bytes-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-little-endian-bytes-20261011-02'", "CURRENT = DIAG / 'transfer-scalar-montgomery-value-20261011-03'")
s=s.replace('transfer-scalar-little-endian-bytes-checkpoint-20261011-02','transfer-scalar-montgomery-value-checkpoint-20261011-03').replace('scalar-little-endian-bytes-endpoint','scalar-montgomery-value-endpoint')
replace("MODULE = 'TransferScalarLittleEndianBytes01'", "MODULE = 'TransferScalarMontgomeryValue01'")
replace('assert len(fresh) == 15','assert len(fresh) == 13')
replace("assert pool['objects'] == 86 and len(pool['inherited_public_reports']) == 811", "assert pool['objects'] == 87 and len(pool['inherited_public_reports']) == 826")
replace("manager_endpoint = DIAG / 'transfer-scalar-masked-normalization-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-scalar-little-endian-bytes-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-masked-normalization-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-little-endian-bytes-endpoint01.tar.xz'")
replace('24641ba1343e6d8fb9fc22414493e7507212f25673829d61c38426eb4ac541cd','f1b880a3e10f1185e104962f83bc2616b69a5304791b41011708f7097c285b1e')
replace("tar.extractfile('reports/fresh-10-complete-declarations.txt')", "tar.extractfile('reports/fresh-15-complete-declarations.txt')")
replace('assert len(manager_reports) == 10','assert len(manager_reports) == 15')
replace("'module': 'TransferScalarMaskedNormalization01'", "'module': 'TransferScalarLittleEndianBytes01'")
replace('assert len(combined_reports) == 811','assert len(combined_reports) == 826')
replace('assert len(manager_selected) == 86','assert len(manager_selected) == 87')
replace("reference = {'scalar_masked_normalization':", "reference = {'scalar_little_endian_bytes':")
replace("'imported_complete_reports': 10", "'imported_complete_reports': 15")
replace("'complete_owned_modules': 86, 'inherited_complete_reports': 811", "'complete_owned_modules': 87, 'inherited_complete_reports': 826")
s=s.replace('eighty-six-module','eighty-seven-module').replace('811 original inherited','826 original inherited').replace('verified 811 inherited','verified 826 inherited')
replace("'fresh_definition_audits': 6", "'fresh_definition_audits': 2")
replace("'fresh_theorem_audits': 9", "'fresh_theorem_audits': 11")
replace("'fresh_complete_public_audits': 15", "'fresh_complete_public_audits': 13")
replace("'inherited_complete_public_audits': 811", "'inherited_complete_public_audits': 826")
replace("'fresh_audits': 15, 'inherited_audits': 811", "'fresh_audits': 13, 'inherited_audits': 826",2)
replace("'rejected_attempts': 1", "'rejected_attempts': 2")
s=s.replace('SOURCE_SCALAR_TYPED_LITTLE_ENDIAN_32_BYTE_CANONICAL_PROJECTION_QUALIFIED','SOURCE_SCALAR_EXACT_CANONICAL_MONTGOMERY_VALUE_QUALIFIED')
s=s.replace('transfer-scalar-little-endian-bytes-20261011-01','transfer-scalar-montgomery-value-20261011-01').replace('TransferScalarLittleEndianBytes01.lean','TransferScalarMontgomeryValue01.lean').replace('runs/01-TransferScalarLittleEndianBytes01/stdout.txt','runs/01-TransferScalarMontgomeryValue01/stdout.txt')
replace("'events.jsonl','context/serializer-byte-shape.json','handwritten/TransferScalarMontgomeryValue01.lean'", "'events.jsonl','handwritten/TransferScalarMontgomeryValue01.lean'")
s=s.replace('two wrapper width rewrites needed wordBytes unfolding; all raw diagnostics, zero proof/control credit','looping modular simp and unreduced congrArg/modular rewrite errors; full raw diagnostics, zero proof/control credit')
s=s.replace('exact proof-only two wordBytes unfolding repair derivation source','exact maintained two-attempt proof-only modular/radix notation repair derivation source')
replace("add(stdout, 'reports/fresh-15-complete-declarations.txt'", "add(stdout, 'reports/fresh-13-complete-declarations.txt'")
anchor="add(stdout, 'reports/fresh-13-complete-declarations.txt'"
extra='''failed02=DIAG/'transfer-scalar-montgomery-value-20261011-02'
for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarMontgomeryValue01.lean','project/ShielddSecurity/TransferScalarMontgomeryValue01.lean','runs/01-TransferScalarMontgomeryValue01/stdout.txt']:
    assert pin(failed02/n) in plan['pins']
    add(failed02/n,'rejected/02/'+n,'finite bound rewrite needed exact radix64 notation; full raw diagnostics, zero proof/control credit')
'''
s=s.replace(anchor,extra+anchor,1)
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Thirteen complete full type/axiom reports retained. Failed01/02 exact raw errors/reports retained with zero credit; fresh03 proof-only modular rewrites, congrArg reduction and explicit low-word radix64 bound leave all thirteen contracts unchanged. Source-shaped exact canonical Montgomery value proved using small symbolic recurrence and closed integer certificates. Rust primitive/native trace/Scalar interpretation/runtime projection remain separate correspondence obligations. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('typed UInt8 LE recurrence, exact finite four-word source-shaped serializer width and canonical value','derived source INV cancellation, exact divisible round equation, symbolic modular walk and exact canonical Montgomery scalar value')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':13,'inherited_reports':826,'owned_modules':87,'rejected_attempts':2})
