from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-word-object-read-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-word-object-read-20261011-03'","CURRENT = DIAG / 'transfer-checked-word-publication-20261011-01'"),
 ("MODULE = 'TransferWordObjectRead01'","MODULE = 'TransferCheckedWordPublication01'"),
 ("CHECKPOINT = DIAG / 'transfer-word-object-read-checkpoint-20261011-03'","CHECKPOINT = DIAG / 'transfer-checked-word-publication-checkpoint-20261011-01'"),
 ('assert len(fresh) == 8','assert len(fresh) == 2'),
 ("assert pool['objects'] == 120 and len(pool['inherited_public_reports']) == 1036","assert pool['objects'] == 121 and len(pool['inherited_public_reports']) == 1044"),
 ("manager_endpoint = DIAG / 'transfer-word-source-driver-endpoint-20261011-03'","manager_endpoint = DIAG / 'transfer-word-object-read-endpoint-20261011-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-word-source-driver-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-word-object-read-endpoint01.tar.xz'"),
 ('edb48a6ad5d6f6588575f18ff90f7940242d2971173f0224ea5fb11495dbed87','c3974f41d5c2f922066f6119017936606042633c1a0b97f5ed41792c219082e9'),
 ("tar.extractfile('reports/fresh-5-complete-declarations.txt')","tar.extractfile('reports/fresh-8-complete-declarations.txt')"),
 ('assert len(manager_reports) == 5','assert len(manager_reports) == 8'),
 ("'module': 'TransferWordSourceDriver01'","'module': 'TransferWordObjectRead01'"),
 ('assert len(combined_reports) == 1036','assert len(combined_reports) == 1044'),
 ('assert len(manager_selected) == 120','assert len(manager_selected) == 121'),
 ("reference = {'word_source_driver':","reference = {'word_object_read':"),
 ("'imported_complete_reports': 5","'imported_complete_reports': 8"),
 ("'complete_owned_modules': 120, 'inherited_complete_reports': 1036","'complete_owned_modules': 121, 'inherited_complete_reports': 1044"),
 ("'fresh_definition_audits': 3","'fresh_definition_audits': 1"),
 ("'fresh_theorem_audits': 5","'fresh_theorem_audits': 1"),
 ("'fresh_complete_public_audits': 8","'fresh_complete_public_audits': 2"),
 ("'inherited_complete_public_audits': 1036","'inherited_complete_public_audits': 1044"),
 ("'rejected_attempts': 1, 'unrun_setup_attempts': 1","'rejected_attempts': 0"),
 ("archive = ROOT / 'portable-windows-word-object-read-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-checked-word-publication-endpoint01.tar.xz'"),
 ("add(stdout, 'reports/fresh-8-complete-declarations.txt'","add(stdout, 'reports/fresh-2-complete-declarations.txt'")]:replace(a,b)
replace("'fresh_audits': 8, 'inherited_audits': 1036","'fresh_audits': 2, 'inherited_audits': 1044",2)
s=s.replace('transfer-word-object-read-endpoint-v1','transfer-checked-word-publication-endpoint-v1').replace('one-hundred-twenty-module','one-hundred-twenty-one-module').replace('1036 original inherited','1044 original inherited').replace('verified 1036 inherited','verified 1044 inherited')
s=s.replace('CHECKED_TYPED_WORD_OBJECT_GETTER_PANIC_AND_TOMBSTONE_BRANCHES_QUALIFIED','RETURNED_WHOLE_WORD_DRIVER_DERIVES_CHECKED_PENDING_GETTER_AND_BOUNDARY_QUALIFIED')
start=s.index('for attempt,names in [(1,');end=s.index("row=mapping['checked_pending_read_source_shape']",start)
s=s[:start]+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Two first-pass complete full type/axiom reports retained, one definition/one whole theorem. Actual transferred pending word object and its canonical bounded input vector derive successful checked getter on reached state, with exact frozen/application/physical Ready/Idle commit boundary. No desired final object, walk/current state, codec/getter/domain/type-success premise supplied to returned theorem. Unsupported ghost and wrong typed object never default under checked native-entry model; no global native ghost erasure claim. Prior setup/pressure histories remain immutable ancestral archive/pins. Actual Any/downcast/Clone/imbl/Scalar/compiler/Choice/CtOption/ownership/snapshot/ICS23/OS/full trace bindings remain explicit. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':2,'inherited_reports':1044,'owned_modules':121,'first_pass':True})
