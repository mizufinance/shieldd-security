"""Seal generated source key/FORMAT binding and independent regeneration."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-stage-boundary-source-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-stage-boundary-source-20261011-02'", "CURRENT = DIAG / 'transfer-boundary-key-binding-20261011-01'")
s=s.replace('transfer-stage-boundary-source-checkpoint-20261011-02','transfer-boundary-key-binding-checkpoint-20261011-01')
s=s.replace('stage-boundary-source-endpoint','boundary-key-binding-endpoint')
replace("MODULE = 'TransferStageBoundarySource01'", "MODULE = 'TransferBoundaryKeyBinding01'")
replace('assert len(fresh) == 15','assert len(fresh) == 11')
replace("assert pool['objects'] == 52 and len(pool['inherited_public_reports']) == 518", "assert pool['objects'] == 53 and len(pool['inherited_public_reports']) == 533")
replace("manager_endpoint = DIAG / 'transfer-store-commit-source-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-stage-boundary-source-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-store-commit-source-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-stage-boundary-source-endpoint01.tar.xz'")
replace('1038ed26a046ff56c48e1dc86fe6f2b7b21e447637f07e95a7e26ed82a93330b','76f725add575c25a160f3042fdb5d8ba7abe97224c3c08f0671ba4e32e3ee4c5')
replace("tar.extractfile('reports/fresh-13-complete-declarations.txt')", "tar.extractfile('reports/fresh-15-complete-declarations.txt')")
replace('assert len(manager_reports) == 13','assert len(manager_reports) == 15')
replace("'module': 'TransferStoreCommitSource01'", "'module': 'TransferStageBoundarySource01'")
replace('assert len(combined_reports) == 518','assert len(combined_reports) == 533')
replace('assert len(manager_selected) == 52','assert len(manager_selected) == 53')
replace("reference = {'store_commit_source':", "reference = {'stage_boundary_source':")
replace("'imported_complete_reports': 13", "'imported_complete_reports': 15")
replace("'complete_owned_modules': 52, 'inherited_complete_reports': 518", "'complete_owned_modules': 53, 'inherited_complete_reports': 533")
s=s.replace('Exact fifty-two-module whole/current pending/durable reader/source capacity/block/seal/prepare/finite codec/writer/intent/participants/boundary staging closure, with 518 original inherited complete reports', 'Exact fifty-three-module whole/current pending/durable reader/source capacity/block/seal/prepare/finite codec/writer/intent/participants/boundary staging/source literal closure, with 533 original inherited complete reports')
replace("add(stdout, 'reports/fresh-15-complete-declarations.txt'", "add(stdout, 'reports/fresh-11-complete-declarations.txt'")
replace("add(CURRENT / ('handwritten/' + MODULE + '.lean')", "add(CURRENT / ('generated/' + MODULE + '.lean')")
s=s.replace('source transition validation/initialization/three writes/stage installation definitions and six exact frame/value/guard/preparation/writer stage proofs','generated exact source key/FORMAT bytes and three byte/separation/actual-stage exact-value proofs')
s=s.replace('complete fifty-two-module first import root','complete fifty-three-module first import root')
s=s.replace('verified 518 inherited reports','verified 533 inherited reports')
s=s.replace('SOURCE_STAGE_BOUNDARY_VALIDATION_PARENT_GATES_AND_EXACT_WRITES_QUALIFIED','SOURCE_BOUNDARY_LITERAL_KEYS_FORMAT_AND_EXACT_STAGE_WRITES_QUALIFIED')
replace("'fresh_definition_audits': 9", "'fresh_definition_audits': 8")
replace("'fresh_theorem_audits': 6", "'fresh_theorem_audits': 3")
replace("'fresh_complete_public_audits': 15", "'fresh_complete_public_audits': 11")
replace("'inherited_complete_public_audits': 518", "'inherited_complete_public_audits': 533")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All eleven declarations have original complete type/axiom reports, maintained literal generator and byte-identical independent regeneration. Exact source key separation derives concrete stored serialized next boundary, FORMAT and observed aggregate-root bytes after actual source stage success. Native key/getter/serde/crypto/type/owner/durability remains explicit; zero native/control/full certification credit.'}"+s[end:]
s=s.replace("'fresh_audits': 15, 'inherited_audits': 518", "'fresh_audits': 11, 'inherited_audits': 533")
start=s.index("add(CURRENT / 'repair_recipe.py'"); end=s.index("mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())",start)
extra="""regenerated = DIAG / 'transfer-boundary-key-regeneration-20261011-01'
assert (regenerated / 'generated' / (MODULE + '.lean')).read_bytes() == (CURRENT / 'generated' / (MODULE + '.lean')).read_bytes()
for name in ['generate.py', 'generation.json']:
    add(CURRENT / name, 'generator/' + name, 'maintained literal extraction and complete generation input/output identities')
for name in ['generation.json', 'generated/' + MODULE + '.lean']:
    add(regenerated / name, 'independent-regeneration/' + name, 'separate byte-identical generator invocation; no generated hand edits')
"""
s=s[:start]+extra+s[end:]
s=s.replace("'rejected_attempts': 1", "'rejected_attempts': 0")
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':11,'inherited_reports':533,'owned_modules':53,'regeneration':True})
