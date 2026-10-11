"""Seal exact source padding/carry model; preserve pressure stop and failed rewrite attempt."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-typed-scalar-publication-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-typed-scalar-publication-20261011-01'", "CURRENT = DIAG / 'transfer-scalar-padded-carry-20261011-03'")
s=s.replace('transfer-typed-scalar-publication-checkpoint-20261011-01','transfer-scalar-padded-carry-checkpoint-20261011-03').replace('typed-scalar-publication-endpoint','scalar-padded-carry-endpoint')
replace("MODULE = 'TransferTypedScalarPublication01'", "MODULE = 'TransferScalarPaddedCarry01'")
replace('assert len(fresh) == 3','assert len(fresh) == 6')
replace("assert pool['objects'] == 88 and len(pool['inherited_public_reports']) == 839", "assert pool['objects'] == 89 and len(pool['inherited_public_reports']) == 842")
replace("manager_endpoint = DIAG / 'transfer-scalar-montgomery-value-endpoint-20261011-03'", "manager_endpoint = DIAG / 'transfer-typed-scalar-publication-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-scalar-montgomery-value-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-typed-scalar-publication-endpoint01.tar.xz'")
replace('c48723ab396d4170e0bf0cbc8ca4f950ea06b24af7d912f22bf0c4a9a7d165b6','ac74e64e72236e0afa9700349fbfba007c3a8d7b6b8e68663eed51f3659fce57')
replace("tar.extractfile('reports/fresh-13-complete-declarations.txt')", "tar.extractfile('reports/fresh-3-complete-declarations.txt')")
replace('assert len(manager_reports) == 13','assert len(manager_reports) == 3')
replace("'module': 'TransferScalarMontgomeryValue01'", "'module': 'TransferTypedScalarPublication01'")
replace('assert len(combined_reports) == 839','assert len(combined_reports) == 842')
replace('assert len(manager_selected) == 88','assert len(manager_selected) == 89')
replace("reference = {'scalar_montgomery_value':", "reference = {'typed_scalar_publication':")
replace("'imported_complete_reports': 13", "'imported_complete_reports': 3")
replace("'complete_owned_modules': 88, 'inherited_complete_reports': 839", "'complete_owned_modules': 89, 'inherited_complete_reports': 842")
s=s.replace('eighty-eight-module','eighty-nine-module').replace('839 original inherited','842 original inherited').replace('verified 839 inherited','verified 842 inherited')
replace("'fresh_definition_audits': 0", "'fresh_definition_audits': 3")
replace("'fresh_complete_public_audits': 3", "'fresh_complete_public_audits': 6")
replace("'inherited_complete_public_audits': 839", "'inherited_complete_public_audits': 842")
replace("'fresh_audits': 3, 'inherited_audits': 839", "'fresh_audits': 6, 'inherited_audits': 842",2)
replace("'rejected_attempts': 0", "'rejected_attempts': 2")
s=s.replace('SOURCE_TYPED_SCALAR_EXACT_PUBLICATION_JOIN_QUALIFIED','SOURCE_SCALAR_EXPLICIT_PADDED_MAC_ADC_CARRY_SCHEDULE_QUALIFIED')
replace("add(stdout, 'reports/fresh-3-complete-declarations.txt'", "add(stdout, 'reports/fresh-6-complete-declarations.txt'")
anchor="add(stdout, 'reports/fresh-6-complete-declarations.txt'"
extra='''add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact maintained proof-only let reduction source, guards unchanged')
failed01=DIAG/'transfer-scalar-padded-carry-20261011-01'
failedEvents=[json.loads(x) for x in (failed01/'events.jsonl').read_text().splitlines()]
assert failedEvents[-1]['result']['status']=='failed' and failedEvents[-1]['result']['reason']=='Physical memory pressure'
assert not (failed01/'runs/01-TransferScalarPaddedCarry01/stdout.txt').exists()
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarPaddedCarry01.lean','project/ShielddSecurity/TransferScalarPaddedCarry01.lean']:
    assert pin(failed01/n) in plan['pins']
    add(failed01/n,'rejected/01/'+n,'owned physical-memory monitor stop before stdout was saved; no proof/control credit')
failed02=DIAG/'transfer-scalar-padded-carry-20261011-02'
assert (failed01/'handwritten/TransferScalarPaddedCarry01.lean').read_bytes()==(failed02/'handwritten/TransferScalarPaddedCarry01.lean').read_bytes()
for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarPaddedCarry01.lean','project/ShielddSecurity/TransferScalarPaddedCarry01.lean','runs/01-TransferScalarPaddedCarry01/stdout.txt']:
    assert pin(failed02/n) in plan['pins']
    add(failed02/n,'rejected/02/'+n,'identical fresh attempt reached Lean; local bindings prevented exact ADC rewrite; raw reports/error retained, zero credit')
'''
s=s.replace(anchor,extra+anchor,1)
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete full type/axiom reports retained. Failed01 memory-pressure stop preserved with no saved stdout, failed02 identical source/full raw rewrite error preserved; both zero credit. Fresh03 proof-only local binding reduction leaves six contracts unchanged. Explicit source padding recurrence derives every ignored carry zero and exact serializer, retaining Rust primitive/native trace/compiler/type/library correspondence obligations. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('typed action projection derives canonical key bounds and exact ordered mathematical input/publication vector','explicit padded MAC/ADC source schedule derives all zero ignored carries, exact 32-byte canonical Montgomery serializer')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':842,'owned_modules':89,'fresh_rejected_attempts':2})
