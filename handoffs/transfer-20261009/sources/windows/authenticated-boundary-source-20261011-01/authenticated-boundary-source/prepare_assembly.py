"""Seal source authenticated snapshot composition with explicit value coherence."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-boundary-reader-source-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("CURRENT = DIAG / 'transfer-boundary-reader-source-20261011-02'", "CURRENT = DIAG / 'transfer-authenticated-boundary-source-20261011-01'")
s=s.replace('transfer-boundary-reader-source-checkpoint-20261011-02','transfer-authenticated-boundary-source-checkpoint-20261011-01')
s=s.replace('boundary-reader-source-endpoint','authenticated-boundary-source-endpoint')
replace("MODULE = 'TransferBoundaryReaderSource01'", "MODULE = 'TransferAuthenticatedBoundarySource01'")
replace('assert len(fresh) == 7','assert len(fresh) == 9')
replace("assert pool['objects'] == 54 and len(pool['inherited_public_reports']) == 544", "assert pool['objects'] == 55 and len(pool['inherited_public_reports']) == 551")
replace("manager_endpoint = DIAG / 'transfer-boundary-key-binding-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-boundary-reader-source-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-boundary-key-binding-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-boundary-reader-source-endpoint01.tar.xz'")
replace('27ae0215e95b37b8142d00ede68807b4cf6e5332a9ec69636b316a542adb7098','928eee7e3e07762fae8f6a8f496f8fe887d5b2d3ed371303e5c903a78c43a937')
replace("tar.extractfile('reports/fresh-11-complete-declarations.txt')", "tar.extractfile('reports/fresh-7-complete-declarations.txt')")
replace('assert len(manager_reports) == 11','assert len(manager_reports) == 7')
replace("'module': 'TransferBoundaryKeyBinding01'", "'module': 'TransferBoundaryReaderSource01'")
replace('assert len(combined_reports) == 544','assert len(combined_reports) == 551')
replace('assert len(manager_selected) == 54','assert len(manager_selected) == 55')
replace("reference = {'boundary_key_binding':", "reference = {'boundary_reader_source':")
replace("'imported_complete_reports': 11", "'imported_complete_reports': 7")
replace("'complete_owned_modules': 54, 'inherited_complete_reports': 544", "'complete_owned_modules': 55, 'inherited_complete_reports': 551")
s=s.replace('Exact fifty-four-module whole/current pending/durable reader/source capacity/block/seal/prepare/finite codec/writer/intent/participants/boundary staging/keys/source reader closure, with 544 original inherited complete reports', 'Exact fifty-five-module whole/current pending/durable reader/source capacity/block/seal/prepare/finite codec/writer/intent/participants/boundary staging/keys/reader/authenticated snapshot closure, with 551 original inherited complete reports')
replace("add(stdout, 'reports/fresh-7-complete-declarations.txt'", "add(stdout, 'reports/fresh-9-complete-declarations.txt'")
s=s.replace('source actual boundary reader/stage reader installation definitions and four source observation/refusal/staging proofs','source snapshot/key authentication recurrence/actual boundary and height program definitions and four derived source call/value coherence proofs')
s=s.replace('complete fifty-four-module first import root','complete fifty-five-module first import root')
s=s.replace('verified 544 inherited reports','verified 551 inherited reports')
s=s.replace('SOURCE_BOUNDARY_READER_ACTUAL_BYTES_FORMAT_DECODE_HEIGHT_AND_ROOTS_QUALIFIED','SOURCE_AUTHENTICATED_BOUNDARY_ROOT_KEY_PROOFS_READER_HEIGHT_AND_VALUE_COHERENCE_QUALIFIED')
replace("'fresh_definition_audits': 3", "'fresh_definition_audits': 5")
replace("'fresh_complete_public_audits': 7", "'fresh_complete_public_audits': 9")
replace("'inherited_complete_public_audits': 544", "'inherited_complete_public_audits': 551")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' All nine declarations have original complete type/axiom reports. Whole source success derives actual root equality, ordered key authentication, actual source reader and observed height agreement. Raw value membership uses separate explicit immutable snapshot consistency and verifier soundness contracts. Native ICS23/path/spec/value/type/key/root/owner/async/durability remains interfaces; zero native/control/full certification credit.'}"+s[end:]
s=s.replace("'fresh_audits': 7, 'inherited_audits': 544", "'fresh_audits': 9, 'inherited_audits': 551")
start=s.index("add(CURRENT / 'repair_recipe.py'"); end=s.index("mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())",start)
s=s[:start]+s[end:]
s=s.replace("'rejected_attempts': 1", "'rejected_attempts': 0")
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':9,'inherited_reports':551,'owned_modules':55})
