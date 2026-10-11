"""Seal symbolic injective key renaming and core-only congruence repair."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-installed-source-publication-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-installed-source-publication-20261011-02'", "CURRENT = DIAG / 'transfer-injective-key-publication-20261011-02'")
s=s.replace('transfer-installed-source-publication-checkpoint-20261011-02','transfer-injective-key-publication-checkpoint-20261011-02').replace('installed-source-publication-endpoint','injective-key-publication-endpoint')
replace("MODULE = 'TransferInstalledSourcePublication01'", "MODULE = 'TransferInjectiveKeyPublication01'")
replace('assert len(fresh) == 7','assert len(fresh) == 6')
replace("assert pool['objects'] == 94 and len(pool['inherited_public_reports']) == 873", "assert pool['objects'] == 95 and len(pool['inherited_public_reports']) == 880")
replace("manager_endpoint = DIAG / 'transfer-known-finalizer-publication-endpoint-20261011-03'", "manager_endpoint = DIAG / 'transfer-installed-source-publication-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-known-finalizer-publication-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-installed-source-publication-endpoint01.tar.xz'")
replace('e77c384ce26dee74657dcc6e40f1244a5f7bd4e3b29789c66b8a0f1757ad6582','f5efd615d96a7d130d2b46963e56326a50299921594a4bad426f9aa9876b409b')
replace("'module': 'TransferKnownFinalizerPublication01'", "'module': 'TransferInstalledSourcePublication01'")
replace('assert len(combined_reports) == 873','assert len(combined_reports) == 880')
replace('assert len(manager_selected) == 94','assert len(manager_selected) == 95')
replace("reference = {'concrete_known_finalizer_publication':", "reference = {'installed_source_publication':")
replace("'complete_owned_modules': 94, 'inherited_complete_reports': 873", "'complete_owned_modules': 95, 'inherited_complete_reports': 880")
s=s.replace('ninety-four-module','ninety-five-module').replace('873 original inherited','880 original inherited').replace('verified 873 inherited','verified 880 inherited')
replace("'fresh_structure_audits': 1", "'fresh_structure_audits': 0")
replace("'fresh_complete_public_audits': 7", "'fresh_complete_public_audits': 6")
replace("'inherited_complete_public_audits': 873", "'inherited_complete_public_audits': 880")
replace("'fresh_audits': 7, 'inherited_audits': 873", "'fresh_audits': 6, 'inherited_audits': 880",2)
s=s.replace('SOURCE_INSTALLED_TYPED_REQUEST_AND_FINALIZER_PUBLICATION_QUALIFIED','SOURCE_INJECTIVE_NATURAL_KEY_LABEL_PUBLICATION_QUALIFIED')
start=s.index("add(CURRENT/'recipe_source.py'");end=s.index("add(stdout, 'reports/fresh-7-complete-declarations.txt'",start)
extra="""add(CURRENT/'recipe_source.py','qualified/recipe_source.py','exact core-only congrArg repair source; finite guards unchanged')
failed=DIAG/'transfer-injective-key-publication-20261011-01'
for n in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferInjectiveKeyPublication01.lean','project/ShielddSecurity/TransferInjectiveKeyPublication01.lean','runs/01-TransferInjectiveKeyPublication01/stdout.txt']:
    assert pin(failed/n) in plan['pins']
    add(failed/n,'rejected-kernel/01/'+n,'unavailable congrArg2 helper compiler failure; zero proof/control credit')
old=(failed/'handwritten/TransferInjectiveKeyPublication01.lean').read_text()
assert old.replace('exact congrArg₂ List.cons pair.1 (@ih rest pair.2)', 'exact (congrArg (fun h : Nat => h :: tail) pair.1).trans (congrArg (List.cons other) (@ih rest pair.2))')==(CURRENT/'handwritten/TransferInjectiveKeyPublication01.lean').read_text()
"""
s=s[:start]+extra+s[end:]
replace("add(stdout, 'reports/fresh-7-complete-declarations.txt'", "add(stdout, 'reports/fresh-6-complete-declarations.txt'")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Six complete full type/axiom reports retained. Failed01 unknown congrArg2 helper output retained in full, unselected, zero credit. Fresh02 two core congrArg steps leave six contracts unchanged. Pure recursive key label injection is proved, then installed in complete source request/finalizer publication. Symbolic key renaming does not establish runtime cache/String/hash correspondence. Full native trace/selectors/codec/ownership/OS bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('concrete all-slot source request installation and six-key finalizer derive exact ordered mathematical vector through full modeled publication','proved pure injective byte-list natural labels instantiate exact typed source and finalizer whole publication without caller key injectivity')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':880,'owned_modules':95,'rejected_kernel':1})
