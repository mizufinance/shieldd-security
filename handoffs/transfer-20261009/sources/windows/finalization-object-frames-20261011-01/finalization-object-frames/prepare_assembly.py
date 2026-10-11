"""Seal six-key symbolic object frame proof without replaying ancestors."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-source-typed-input-projection-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-source-typed-input-projection-20261011-03'", "CURRENT = DIAG / 'transfer-finalization-object-frames-20261011-01'")
s=s.replace('transfer-source-typed-input-projection-checkpoint-20261011-03','transfer-finalization-object-frames-checkpoint-20261011-01').replace('source-typed-input-projection-endpoint','finalization-object-frames-endpoint')
replace("MODULE = 'TransferSourceTypedInputProjection01'", "MODULE = 'TransferFinalizationObjectFrames01'")
replace('assert len(fresh) == 6','assert len(fresh) == 8')
replace("assert pool['objects'] == 91 and len(pool['inherited_public_reports']) == 852", "assert pool['objects'] == 92 and len(pool['inherited_public_reports']) == 858")
replace("manager_endpoint = DIAG / 'transfer-scalar-byte-equality-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-source-typed-input-projection-endpoint-20261011-03'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-byte-equality-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-source-typed-input-projection-endpoint01.tar.xz'")
replace('ae5fc3150765b707500168fa6ccb1382d73cb59383680478654775022ab6cf72','f5aad3d0bb7f181149b17cf0f1f8bbc984180edb15034f82be3414c3a430857f')
replace("tar.extractfile('reports/fresh-4-complete-declarations.txt')", "tar.extractfile('reports/fresh-6-complete-declarations.txt')")
replace('assert len(manager_reports) == 4','assert len(manager_reports) == 6')
replace("'module': 'TransferScalarByteEquality01'", "'module': 'TransferSourceTypedInputProjection01'")
replace('assert len(combined_reports) == 852','assert len(combined_reports) == 858')
replace('assert len(manager_selected) == 91','assert len(manager_selected) == 92')
replace("reference = {'scalar_byte_equality':", "reference = {'source_typed_input_projection':")
replace("'imported_complete_reports': 4", "'imported_complete_reports': 6")
replace("'complete_owned_modules': 91, 'inherited_complete_reports': 852", "'complete_owned_modules': 92, 'inherited_complete_reports': 858")
s=s.replace('ninety-one-module','ninety-two-module').replace('852 original inherited','858 original inherited').replace('verified 852 inherited','verified 858 inherited')
replace("'fresh_theorem_audits': 3", "'fresh_structure_audits': 1, 'fresh_theorem_audits': 4")
replace("'fresh_complete_public_audits': 6", "'fresh_complete_public_audits': 8")
replace("'inherited_complete_public_audits': 852", "'inherited_complete_public_audits': 858")
replace("'fresh_audits': 6, 'inherited_audits': 852", "'fresh_audits': 8, 'inherited_audits': 858",2)
replace("'rejected_attempts': 2", "'rejected_attempts': 0")
s=s.replace('SOURCE_TRANSFER_CONCRETE_TYPED_INPUT_PROJECTION_QUALIFIED','SOURCE_KNOWN_FINALIZATION_OBJECT_FRAMES_QUALIFIED')
start=s.index("add(CURRENT/'recipe_source.py'")
end=s.index("add(stdout, 'reports/fresh-6-complete-declarations.txt'",start)
s=s[:start]+s[end:]
replace("add(stdout, 'reports/fresh-6-complete-declarations.txt'", "add(stdout, 'reports/fresh-8-complete-declarations.txt'")
anchor="row = mapping['action_projection_source_association']"
s=s.replace(anchor,"row = mapping['known_finalization_source_association']\nassert pin(row['path']) == row and row in plan['pins']\nadd(row['path'], 'context/known-finalization-source-association.json', 'six exact source literals and known put/delete call shapes; static association, no exhaustive native trace proof')\n"+anchor,1)
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained. Exact six known key separation and symbolic put/deletion tombstone walk derive pending observation retention; already sealed initial object is preserved. Full trace completeness/order/value/execution and all native bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('concrete all-slot ordered typed input configuration derives mathematical keys and canonical bounds','six-key symbolic put/deletion tombstone trace preserves the same sealed native pending object')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':858,'owned_modules':92,'fresh_rejected_attempts':0})
