"""Seal concrete all-slot ordered typed source projection and immutable proof repairs."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-byte-equality-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-scalar-byte-equality-20261011-01'", "CURRENT = DIAG / 'transfer-source-typed-input-projection-20261011-03'")
s=s.replace('transfer-scalar-byte-equality-checkpoint-20261011-01','transfer-source-typed-input-projection-checkpoint-20261011-03').replace('scalar-byte-equality-endpoint','source-typed-input-projection-endpoint')
replace("MODULE = 'TransferScalarByteEquality01'", "MODULE = 'TransferSourceTypedInputProjection01'")
replace('assert len(fresh) == 4','assert len(fresh) == 6')
replace("assert pool['objects'] == 90 and len(pool['inherited_public_reports']) == 848", "assert pool['objects'] == 91 and len(pool['inherited_public_reports']) == 852")
replace("manager_endpoint = DIAG / 'transfer-scalar-padded-carry-endpoint-20261011-03'", "manager_endpoint = DIAG / 'transfer-scalar-byte-equality-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-padded-carry-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-scalar-byte-equality-endpoint01.tar.xz'")
replace('c01c30c9ce719a65eac427328322b895868ebbfd146f3e641dfbf8381c41e175','ae5fc3150765b707500168fa6ccb1382d73cb59383680478654775022ab6cf72')
replace("tar.extractfile('reports/fresh-6-complete-declarations.txt')", "tar.extractfile('reports/fresh-4-complete-declarations.txt')")
replace('assert len(manager_reports) == 6','assert len(manager_reports) == 4')
replace("'module': 'TransferScalarPaddedCarry01'", "'module': 'TransferScalarByteEquality01'")
replace('assert len(combined_reports) == 848','assert len(combined_reports) == 852')
replace('assert len(manager_selected) == 90','assert len(manager_selected) == 91')
replace("reference = {'scalar_padded_carry':", "reference = {'scalar_byte_equality':")
replace("'imported_complete_reports': 6", "'imported_complete_reports': 4")
replace("'complete_owned_modules': 90, 'inherited_complete_reports': 848", "'complete_owned_modules': 91, 'inherited_complete_reports': 852")
s=s.replace('ninety-module','ninety-one-module').replace('848 original inherited','852 original inherited').replace('verified 848 inherited','verified 852 inherited')
replace("'fresh_definition_audits': 0", "'fresh_definition_audits': 3")
replace("'fresh_theorem_audits': 4", "'fresh_theorem_audits': 3")
replace("'fresh_complete_public_audits': 4", "'fresh_complete_public_audits': 6")
replace("'inherited_complete_public_audits': 848", "'inherited_complete_public_audits': 852")
replace("'fresh_audits': 4, 'inherited_audits': 848", "'fresh_audits': 6, 'inherited_audits': 852",2)
replace("'rejected_attempts': 0", "'rejected_attempts': 2")
s=s.replace('SOURCE_SCALAR_TYPED_BYTE_KEY_VALUE_EQUALITY_QUALIFIED','SOURCE_TRANSFER_CONCRETE_TYPED_INPUT_PROJECTION_QUALIFIED')
replace("add(stdout, 'reports/fresh-4-complete-declarations.txt'", "add(stdout, 'reports/fresh-6-complete-declarations.txt'")
anchor="add(stdout, 'reports/fresh-6-complete-declarations.txt'"
extra='''add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact targeted map-composition proof repair source; all guards unchanged')
for index in [1,2]:
    failed=DIAG/('transfer-source-typed-input-projection-20261011-'+str(index).zfill(2))
    names=['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/source-projection-shape.json','handwritten/TransferSourceTypedInputProjection01.lean','project/ShielddSecurity/TransferSourceTypedInputProjection01.lean','runs/01-TransferSourceTypedInputProjection01/stdout.txt']
    if index==2: names.insert(1,'recipe_source.py')
    for n in names:
        assert pin(failed/n) in plan['pins']
        add(failed/n,'rejected/'+str(index).zfill(2)+'/'+n,'raw map-composition open goal or finite-heartbeat definitional expansion timeout; zero proof/control credit')
'''
s=s.replace(anchor,extra+anchor,1)
anchor="row = mapping['serializer_byte_source_association']"
s=s.replace(anchor,"row = mapping['action_projection_source_association']\nassert pin(row['path']) == row and row in plan['pins']\nadd(row['path'], 'context/action-projection-source-association.json', 'exact input field/all-slot ordered iterator map/batch and Nullifier byte-forwarding shapes; static association only')\n"+anchor,1)
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete full type/axiom reports retained. Failed01 open map-composition goal and failed02 finite-heartbeat whnf timeout preserved in full; zero credit. Fresh03 targeted Function.comp reduction leaves six contracts unchanged and finite guard intact. Installed concrete typed projection yields exact ordered canonical mathematical scalar keys; Rust action/field selectors/iterator/library/compiler/native trace bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('finite typed LE key equality iff exact mathematical Montgomery scalar equality','concrete all-slot ordered typed input configuration derives mathematical keys and canonical bounds')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':852,'owned_modules':91,'fresh_rejected_attempts':2})
