"""Seal exact four-word byte decode and canonical predicate; unrun predecessor retained."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-partition-local-rollback-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-partition-local-rollback-20261011-01'", "CURRENT = DIAG / 'transfer-scalar-byte-decode-20261011-02'")
s=s.replace('transfer-partition-local-rollback-checkpoint-20261011-01','transfer-scalar-byte-decode-checkpoint-20261011-02').replace('partition-local-rollback-endpoint','scalar-byte-decode-endpoint')
replace("MODULE = 'TransferPartitionLocalRollback01'", "MODULE = 'TransferScalarByteDecode01'")
replace('assert len(fresh) == 4','assert len(fresh) == 7')
replace("assert pool['objects'] == 106 and len(pool['inherited_public_reports']) == 943", "assert pool['objects'] == 107 and len(pool['inherited_public_reports']) == 947")
replace("manager_endpoint = DIAG / 'transfer-byte-key-cache-endpoint-20261011-04'", "manager_endpoint = DIAG / 'transfer-partition-local-rollback-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-byte-key-cache-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-partition-local-rollback-endpoint01.tar.xz'")
replace('82ee220d7abecd91552a653ea8e9a4b2e0e690b6230ea9088452225e96afbef7','2da4cb39c290435e018021dd77e20cdc073e9c6af1bfa429e3737ad02c0389c8')
replace("tar.extractfile('reports/fresh-7-complete-declarations.txt')", "tar.extractfile('reports/fresh-4-complete-declarations.txt')")
replace('assert len(manager_reports) == 7','assert len(manager_reports) == 4')
replace("'module': 'TransferByteKeyCache01'", "'module': 'TransferPartitionLocalRollback01'")
replace('assert len(combined_reports) == 943','assert len(combined_reports) == 947')
replace('assert len(manager_selected) == 106','assert len(manager_selected) == 107')
replace("reference = {'byte_key_cache':", "reference = {'partition_local_rollback':")
replace("'imported_complete_reports': 7", "'imported_complete_reports': 4")
replace("'complete_owned_modules': 106, 'inherited_complete_reports': 943", "'complete_owned_modules': 107, 'inherited_complete_reports': 947")
s=s.replace('one-hundred-six-module','one-hundred-seven-module').replace('943 original inherited','947 original inherited').replace('verified 943 inherited','verified 947 inherited')
replace("'fresh_definition_audits': 1", "'fresh_definition_audits': 2")
replace("'fresh_theorem_audits': 3", "'fresh_theorem_audits': 5")
replace("'fresh_complete_public_audits': 4", "'fresh_complete_public_audits': 7")
replace("'inherited_complete_public_audits': 943", "'inherited_complete_public_audits': 947")
replace("'fresh_audits': 4, 'inherited_audits': 943", "'fresh_audits': 7, 'inherited_audits': 947",2)
s=s.replace('SOURCE_PARTITION_LOCAL_ROLLBACK_FRAME_RECOVERY_REUSE_QUALIFIED','SOURCE_TYPED_BYTE_DECODE_CANONICAL_BORROW_QUALIFIED')
at=s.index("add(stdout, 'reports/fresh-4-complete-declarations.txt'")
extra="""add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact reusable canonical range theorem name repair; finite guards unchanged')
oldRoot=DIAG/'transfer-scalar-byte-decode-20261011-01'
assert not (oldRoot/'events.jsonl').exists()
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','context/decoder-shape.json','handwritten/TransferScalarByteDecode01.lean','project/ShielddSecurity/TransferScalarByteDecode01.lean']:
    assert pin(oldRoot/n) in plan['pins']
    add(oldRoot/n,'unrun-predecessor/01/'+n,'theorem-name correction before any kernel invocation; zero credit')
old=(oldRoot/'handwritten/TransferScalarByteDecode01.lean').read_text()
assert old.replace('TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_is_canonical words','TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical words')==(CURRENT/'handwritten/TransferScalarByteDecode01.lean').read_text()
"""
s=s[:at]+extra+s[at:]
replace("add(stdout, 'reports/fresh-4-complete-declarations.txt'", "add(stdout, 'reports/fresh-7-complete-declarations.txt'")
at=s.index("row = mapping['corrected_finalization_source_order']")
s=s[:at]+"row = mapping['scalar_decode_source_shape']\nassert pin(row['path']) == row and row in plan['pins']\nadd(row['path'], 'context/scalar-decoder-shape.json', 'four exact LE word reads/four SBB/low choice bit shape; static source only; R2 conversion separate')\n"+s[at:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Seven complete full type/axiom reports retained. Predecessor01 never invoked; fresh02 reusable theorem-name correction then first kernel attempt passed. Arbitrary exact32byte UInt8 input decoded integer is reconstructed and canonical accept iff below p; exact serializer output passes. Pinned native four LE reads/SBB/choice-bit order association is static only. Actual native from_le_bytes/SBB/Choice/CtOption/Scalar invariant/R2 Montgomery conversion/compiler/full trace binding remains explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('partition-local root update derives forward frame and complete captured/original recovery equivalence','symbolic finite byte-word parser reconstructs exact integer and source-shaped canonical borrow accept predicate')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':947,'owned_modules':107,'first_kernel_passed':True,'unrun_predecessor':1})
