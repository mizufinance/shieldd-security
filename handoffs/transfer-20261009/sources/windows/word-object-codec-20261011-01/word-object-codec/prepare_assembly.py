from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-canonical-word-pending-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
 ("CURRENT = DIAG / 'transfer-canonical-word-pending-20261011-03'","CURRENT = DIAG / 'transfer-word-object-codec-20261011-01'"),
 ("MODULE = 'TransferCanonicalWordPending01'","MODULE = 'TransferWordObjectCodec01'"),
 ("CHECKPOINT = DIAG / 'transfer-canonical-word-pending-checkpoint-20261011-03'","CHECKPOINT = DIAG / 'transfer-word-object-codec-checkpoint-20261011-01'"),
 ("assert pool['objects'] == 117 and len(pool['inherited_public_reports']) == 1015","assert pool['objects'] == 118 and len(pool['inherited_public_reports']) == 1023"),
 ("manager_endpoint = DIAG / 'transfer-symbolic-field-map-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-canonical-word-pending-endpoint-20261011-03'"),
 ("manager_archive = manager_endpoint / 'portable-windows-symbolic-field-map-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-canonical-word-pending-endpoint01.tar.xz'"),
 ('92bcf352e2cc925bcb60911501d9a6ccfcb7bf104434c44098cb9dbc6e400a9e','188197fc7ad7a27c9d2f9b5332f901f8845a2095910f1ce71f238af8312e97f5'),
 ("tar.extractfile('reports/fresh-2-complete-declarations.txt')","tar.extractfile('reports/fresh-8-complete-declarations.txt')"),
 ('assert len(manager_reports) == 2','assert len(manager_reports) == 8'),
 ("'module': 'TransferSymbolicFieldMap01'","'module': 'TransferCanonicalWordPending01'"),
 ('assert len(combined_reports) == 1015','assert len(combined_reports) == 1023'),
 ('assert len(manager_selected) == 117','assert len(manager_selected) == 118'),
 ("reference = {'symbolic_field_map':","reference = {'canonical_word_pending':"),
 ("'imported_complete_reports': 2","'imported_complete_reports': 8"),
 ("'complete_owned_modules': 117, 'inherited_complete_reports': 1015","'complete_owned_modules': 118, 'inherited_complete_reports': 1023"),
 ("'fresh_definition_audits': 3","'fresh_definition_audits': 4"),
 ("'fresh_structure_audits': 1","'fresh_structure_audits': 0"),
 ("'inherited_complete_public_audits': 1015","'inherited_complete_public_audits': 1023"),
 ("'rejected_attempts': 2","'rejected_attempts': 0"),
 ("archive = ROOT / 'portable-windows-canonical-word-pending-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-word-object-codec-endpoint01.tar.xz'")]:replace(a,b)
replace("'fresh_audits': 8, 'inherited_audits': 1015","'fresh_audits': 8, 'inherited_audits': 1023",2)
s=s.replace('transfer-canonical-word-pending-endpoint-v1','transfer-word-object-codec-endpoint-v1').replace('one-hundred-seventeen-module','one-hundred-eighteen-module').replace('1015 original inherited','1023 original inherited').replace('verified 1015 inherited','verified 1023 inherited')
s=s.replace('SOURCE_CONSTRUCTED_CANONICAL_WORD_PENDING_FINITE_CODEC_QUALIFIED','CONCRETE_TYPED_WORD_OBJECT_CODEC_AND_SEALED_GETTER_QUALIFIED')
start=s.index('for attempt in [1,2]:');end=s.index("row = mapping['r2_decoder_payload_source_shape']",start)
s=s[:start]+s[end:]
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight first-pass complete full type/axiom reports retained: four definitions and four theorems. Concrete word-field tag derives supported finite native enum identity and exact restored observations, canonical bounded sealed getter and empty default. Prior field-codec failures remain in immutable ancestral archive/pins; no failed ancestor is counted as a control. Actual native Any/downcast/Clone/imbl/private Scalar/compiler/primitive/Choice/CtOption/ownership/full trace bindings remain explicit. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':1023,'owned_modules':118})
