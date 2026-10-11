"""Seal installed typed source publication and its exact direct-term layout repair."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-known-finalizer-publication-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-known-finalizer-publication-20261011-03'", "CURRENT = DIAG / 'transfer-installed-source-publication-20261011-02'")
s=s.replace('transfer-known-finalizer-publication-checkpoint-20261011-03','transfer-installed-source-publication-checkpoint-20261011-02').replace('known-finalizer-publication-endpoint','installed-source-publication-endpoint')
replace("MODULE = 'TransferKnownFinalizerPublication01'", "MODULE = 'TransferInstalledSourcePublication01'")
replace("assert pool['objects'] == 93 and len(pool['inherited_public_reports']) == 866", "assert pool['objects'] == 94 and len(pool['inherited_public_reports']) == 873")
replace("manager_endpoint = DIAG / 'transfer-finalization-object-frames-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-known-finalizer-publication-endpoint-20261011-03'")
replace("manager_archive = manager_endpoint / 'portable-windows-finalization-object-frames-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-known-finalizer-publication-endpoint01.tar.xz'")
replace('0174a8b0b7033a89cc1909bbdf291a00fad5650b3c00aa7794351a0d591001d7','e77c384ce26dee74657dcc6e40f1244a5f7bd4e3b29789c66b8a0f1757ad6582')
replace("tar.extractfile('reports/fresh-8-complete-declarations.txt')", "tar.extractfile('reports/fresh-7-complete-declarations.txt')")
replace('assert len(manager_reports) == 8','assert len(manager_reports) == 7')
replace("'module': 'TransferFinalizationObjectFrames01'", "'module': 'TransferKnownFinalizerPublication01'")
replace('assert len(combined_reports) == 866','assert len(combined_reports) == 873')
replace('assert len(manager_selected) == 93','assert len(manager_selected) == 94')
replace("reference = {'known_finalization_object_frames':", "reference = {'concrete_known_finalizer_publication':")
replace("'imported_complete_reports': 8", "'imported_complete_reports': 7")
replace("'complete_owned_modules': 93, 'inherited_complete_reports': 866", "'complete_owned_modules': 94, 'inherited_complete_reports': 873")
s=s.replace('ninety-three-module','ninety-four-module').replace('866 original inherited','873 original inherited').replace('verified 866 inherited','verified 873 inherited')
replace("'fresh_definition_audits': 3", "'fresh_definition_audits': 2")
replace("'fresh_theorem_audits': 3", "'fresh_theorem_audits': 4")
replace("'inherited_complete_public_audits': 866", "'inherited_complete_public_audits': 873")
replace("'fresh_audits': 7, 'inherited_audits': 866", "'fresh_audits': 7, 'inherited_audits': 873",2)
replace("'rejected_attempts': 2, 'rejected_setup_attempts': 1, 'rejected_kernel_attempts': 1", "'rejected_attempts': 1, 'rejected_setup_attempts': 0, 'rejected_kernel_attempts': 1")
s=s.replace('SOURCE_CONCRETE_KNOWN_FINALIZER_PUBLICATION_QUALIFIED','SOURCE_INSTALLED_TYPED_REQUEST_AND_FINALIZER_PUBLICATION_QUALIFIED')
start=s.index("add(CURRENT/'recipe_source.py'");end=s.index("add(stdout, 'reports/fresh-7-complete-declarations.txt'",start)
extra="""add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact direct List.isEmpty_map term repair source; all guards unchanged')
failed=DIAG/'transfer-installed-source-publication-20261011-01'
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferInstalledSourcePublication01.lean','project/ShielddSecurity/TransferInstalledSourcePublication01.lean','runs/01-TransferInstalledSourcePublication01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected-kernel/01/'+n,'record proof block parser failure and resulting sorryAx in compiler partial output; all unselected, zero proof/control credit')
old=(failed/'handwritten/TransferInstalledSourcePublication01.lean').read_text()
assert old.replace('nonempty := by\\n    change ((inputs request.base.action).map (fun input => scalarKey (wordOf input))).isEmpty = false\\n    rw [List.isEmpty_map]\\n    exact request.sourceNonempty}', 'nonempty := (List.isEmpty_map (l := inputs request.base.action) (f := fun input => scalarKey (wordOf input))).trans request.sourceNonempty}')==(CURRENT/'handwritten/TransferInstalledSourcePublication01.lean').read_text()
"""
s=s[:start]+extra+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Seven complete full type/axiom reports retained. Failed01 record proof block parser and partial sorryAx output retained in full and unselected; zero credit. Fresh02 direct List.isEmpty_map term leaves seven contracts unchanged. Installed requests derive source projection; installed known finalizer derives retained pending frame; exact source mathematical input vector and whole publication follow. Full native selector/trace/codec/cache/ownership/OS bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('concrete seal/object mutation/V/NV finalizer derives field retention internally and publishes exact global typed mathematical keys','concrete all-slot source request installation and six-key finalizer derive exact ordered mathematical vector through full modeled publication')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':873,'owned_modules':94,'rejected_kernel':1})
