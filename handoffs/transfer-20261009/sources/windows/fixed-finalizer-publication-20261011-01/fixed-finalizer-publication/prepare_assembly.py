"""Seal fixed six-call known source mutation recipe and exact call association."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-injective-key-publication-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-injective-key-publication-20261011-02'", "CURRENT = DIAG / 'transfer-fixed-finalizer-publication-20261011-01'")
s=s.replace('transfer-injective-key-publication-checkpoint-20261011-02','transfer-fixed-finalizer-publication-checkpoint-20261011-01').replace('injective-key-publication-endpoint','fixed-finalizer-publication-endpoint')
replace("MODULE = 'TransferInjectiveKeyPublication01'", "MODULE = 'TransferFixedFinalizerPublication01'")
replace('assert len(fresh) == 6','assert len(fresh) == 8')
replace("assert pool['objects'] == 95 and len(pool['inherited_public_reports']) == 880", "assert pool['objects'] == 96 and len(pool['inherited_public_reports']) == 886")
replace("manager_endpoint = DIAG / 'transfer-installed-source-publication-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-injective-key-publication-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-installed-source-publication-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-injective-key-publication-endpoint01.tar.xz'")
replace('f5efd615d96a7d130d2b46963e56326a50299921594a4bad426f9aa9876b409b','fd52276ef7d0a136533d1fd4cc3393728ba58773ed27bd207d54bce802137657')
replace("tar.extractfile('reports/fresh-7-complete-declarations.txt')", "tar.extractfile('reports/fresh-6-complete-declarations.txt')")
replace('assert len(manager_reports) == 7','assert len(manager_reports) == 6')
replace("'module': 'TransferInstalledSourcePublication01'", "'module': 'TransferInjectiveKeyPublication01'")
replace('assert len(combined_reports) == 880','assert len(combined_reports) == 886')
replace('assert len(manager_selected) == 95','assert len(manager_selected) == 96')
replace("reference = {'installed_source_publication':", "reference = {'injective_key_publication':")
replace("'imported_complete_reports': 7", "'imported_complete_reports': 6")
replace("'complete_owned_modules': 95, 'inherited_complete_reports': 880", "'complete_owned_modules': 96, 'inherited_complete_reports': 886")
s=s.replace('ninety-five-module','ninety-six-module').replace('880 original inherited','886 original inherited').replace('verified 880 inherited','verified 886 inherited')
replace("'fresh_definition_audits': 2", "'fresh_definition_audits': 3")
replace("'fresh_structure_audits': 0", "'fresh_structure_audits': 1")
replace("'fresh_complete_public_audits': 6", "'fresh_complete_public_audits': 8")
replace("'inherited_complete_public_audits': 880", "'inherited_complete_public_audits': 886")
replace("'fresh_audits': 6, 'inherited_audits': 880", "'fresh_audits': 8, 'inherited_audits': 886",2)
replace("'rejected_attempts': 1, 'rejected_setup_attempts': 0, 'rejected_kernel_attempts': 1", "'rejected_attempts': 0")
s=s.replace('SOURCE_INJECTIVE_NATURAL_KEY_LABEL_PUBLICATION_QUALIFIED','SOURCE_FIXED_KNOWN_FINALIZER_PUBLICATION_QUALIFIED')
start=s.index("add(CURRENT/'recipe_source.py'");end=s.index("add(stdout, 'reports/fresh-6-complete-declarations.txt'",start)
s=s[:start]+s[end:]
replace("add(stdout, 'reports/fresh-6-complete-declarations.txt'", "add(stdout, 'reports/fresh-8-complete-declarations.txt'")
anchor="row = mapping['known_finalization_source_association']";assert s.count(anchor)==1
s=s.replace(anchor,"row = mapping['fixed_finalization_source_association']\nassert pin(row['path']) == row and row in plan['pins']\nadd(row['path'], 'context/fixed-finalization-source-association.json', 'exact known returned SCT/compact finishing call-order association, not exhaustive native trace proof')\n"+anchor)
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained. Known six exact source keys and fixed operation order/count/tombstone pattern constructed and proved; caller mutation list and permitted-key proofs eliminated. Actual cached tree object remains native O; complete App trace and hidden callee/native tree/value/codec/cache/selectors/ownership/OS bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
replace('proved pure injective byte-list natural labels instantiate exact typed source and finalizer whole publication without caller key injectivity','fixed known post-seal six source object operations construct exact keys/order/count/tombstones and publish exact global mathematical input vector')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':886,'owned_modules':96,'rejected_kernel':0})
