"""Seal returned complete model block driver and exact witness repair."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-absent-start-publication-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-absent-start-publication-20261011-01'", "CURRENT = DIAG / 'transfer-complete-block-driver-20261011-02'")
s=s.replace('transfer-absent-start-publication-checkpoint-20261011-01','transfer-complete-block-driver-checkpoint-20261011-02').replace('absent-start-publication-endpoint','complete-block-driver-endpoint')
replace("MODULE = 'TransferAbsentStartPublication01'", "MODULE = 'TransferCompleteBlockDriver01'")
replace('assert len(fresh) == 4','assert len(fresh) == 2')
replace("assert pool['objects'] == 99 and len(pool['inherited_public_reports']) == 905", "assert pool['objects'] == 100 and len(pool['inherited_public_reports']) == 909")
replace("manager_endpoint = DIAG / 'transfer-tagged-codec-publication-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-absent-start-publication-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-tagged-codec-publication-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-absent-start-publication-endpoint01.tar.xz'")
replace('5e5fd0c2a0729d95450206f4b460b9f12969d6e95da2c5ebda9c5ce710cbd732','6a0feb331daf7daea2726d9bd73a3fdd656faf4b76caf48d560fcc5cdde63fb3')
replace("tar.extractfile('reports/fresh-8-complete-declarations.txt')", "tar.extractfile('reports/fresh-4-complete-declarations.txt')")
replace('assert len(manager_reports) == 8','assert len(manager_reports) == 4')
replace("'module': 'TransferTaggedCodecPublication01'", "'module': 'TransferAbsentStartPublication01'")
replace('assert len(combined_reports) == 905','assert len(combined_reports) == 909')
replace('assert len(manager_selected) == 99','assert len(manager_selected) == 100')
replace("reference = {'tagged_codec_publication':", "reference = {'absent_start_publication':")
replace("'imported_complete_reports': 8", "'imported_complete_reports': 4")
replace("'complete_owned_modules': 99, 'inherited_complete_reports': 905", "'complete_owned_modules': 100, 'inherited_complete_reports': 909")
s=s.replace('ninety-nine-module','one-hundred-module').replace('905 original inherited','909 original inherited').replace('verified 905 inherited','verified 909 inherited')
replace("'fresh_theorem_audits': 3", "'fresh_theorem_audits': 1")
replace("'fresh_complete_public_audits': 4", "'fresh_complete_public_audits': 2")
replace("'inherited_complete_public_audits': 905", "'inherited_complete_public_audits': 909")
replace("'fresh_audits': 4, 'inherited_audits': 905", "'fresh_audits': 2, 'inherited_audits': 909",2)
s=s.replace('SOURCE_FRESH_ABSENT_PENDING_START_PUBLICATION_QUALIFIED','SOURCE_RETURNED_COMPLETE_BLOCK_DRIVER_PUBLICATION_QUALIFIED')
replace("add(stdout, 'reports/fresh-4-complete-declarations.txt'", "add(stdout, 'reports/fresh-2-complete-declarations.txt'")
at=s.index("add(stdout, 'reports/fresh-2-complete-declarations.txt'")
extra="""add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact case-split reflexive witness repair; finite guards unchanged')
failed=DIAG/'transfer-complete-block-driver-20261011-01'
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferCompleteBlockDriver01.lean','project/ShielddSecurity/TransferCompleteBlockDriver01.lean','runs/01-TransferCompleteBlockDriver01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected-kernel/01/'+n,'case split witness compiler failure; zero proof/control credit')
old=(failed/'handwritten/TransferCompleteBlockDriver01.lean').read_text()
assert old.replace('refine ⟨final, ran, same.symm, ?_⟩','refine ⟨final, rfl, same.symm, ?_⟩')==(CURRENT/'handwritten/TransferCompleteBlockDriver01.lean').read_text()
"""
s=s[:at]+extra+s[at:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Two complete full type/axiom reports retained. Failed01 witness mismatch remains raw and unselected, zero credit; fresh02 changes proof only, two contracts unchanged. Model returned root derives reached native walk state and exact publication witnesses rather than assuming successful walk/current host equality. None grants no failure prefix or rollback credit. FixedFinalizer inherited list remains its defined model; its exact native source-order association is OPEN pending fresh faithful ordering or commuting proof. Native full loop/primitive/field/cache/snapshot/ownership/OS bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('initial absent pending cache and concrete fresh parent publish exact global mathematical inputs without requiring a stored empty pending object','returned whole model driver root derives successful reached walk and exact global mathematical input publication')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':2,'inherited_reports':909,'owned_modules':100,'rejected_kernel':1})
