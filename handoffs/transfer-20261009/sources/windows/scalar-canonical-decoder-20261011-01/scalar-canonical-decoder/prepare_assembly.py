"""Seal first-pass composed actual modeled canonical byte decoder."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-r2-payload-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
("CURRENT = DIAG / 'transfer-scalar-r2-payload-20261011-01'","CURRENT = DIAG / 'transfer-scalar-canonical-decoder-20261011-01'"),
("MODULE = 'TransferScalarR2Payload01'","MODULE = 'TransferScalarCanonicalDecoder01'"),
('assert len(fresh) == 7','assert len(fresh) == 8'),
("assert pool['objects'] == 113 and len(pool['inherited_public_reports']) == 990","assert pool['objects'] == 114 and len(pool['inherited_public_reports']) == 997"),
("manager_endpoint = DIAG / 'transfer-scalar-wide-reduction-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-scalar-r2-payload-endpoint-20261011-01'"),
("manager_archive = manager_endpoint / 'portable-windows-scalar-wide-reduction-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-r2-payload-endpoint01.tar.xz'"),
('326fdd77a0ff7f6c84902fd2fff7a74e8abffefde270f97b2a80cba545339ac4','1c4931d770ee5aa27cd9317703a7064162900a53b4b3a26f4330ea799893319a'),
("tar.extractfile('reports/fresh-8-complete-declarations.txt')","tar.extractfile('reports/fresh-7-complete-declarations.txt')"),
('assert len(manager_reports) == 8','assert len(manager_reports) == 7'),
("'module': 'TransferScalarWideReduction01'","'module': 'TransferScalarR2Payload01'"),
('assert len(combined_reports) == 990','assert len(combined_reports) == 997'),
('assert len(manager_selected) == 113','assert len(manager_selected) == 114'),
("reference = {'scalar_wide_reduction':","reference = {'scalar_r2_payload':"),
("'imported_complete_reports': 8","'imported_complete_reports': 7"),
("'complete_owned_modules': 113, 'inherited_complete_reports': 990","'complete_owned_modules': 114, 'inherited_complete_reports': 997"),
("'fresh_definition_audits': 2","'fresh_definition_audits': 3"),
("'fresh_complete_public_audits': 7","'fresh_complete_public_audits': 8"),
("'inherited_complete_public_audits': 990","'inherited_complete_public_audits': 997"),
("add(stdout, 'reports/fresh-7-complete-declarations.txt'","add(stdout, 'reports/fresh-8-complete-declarations.txt'"),
("archive = ROOT / 'portable-windows-scalar-r2-payload-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-canonical-decoder-endpoint01.tar.xz'")]:replace(a,b)
replace("'fresh_audits': 7, 'inherited_audits': 990","'fresh_audits': 8, 'inherited_audits': 997",2)
s=s.replace('transfer-scalar-r2-payload-checkpoint-20261011-01','transfer-scalar-canonical-decoder-checkpoint-20261011-01').replace('transfer-scalar-r2-payload-endpoint-v1','transfer-scalar-canonical-decoder-endpoint-v1').replace('one-hundred-thirteen-module','one-hundred-fourteen-module').replace('990 original inherited','997 original inherited').replace('verified 990 inherited','verified 997 inherited')
s=s.replace('SOURCE_EXACT_R2_MODELED_DECODER_PAYLOAD_QUALIFIED','SOURCE_CONSTRUCTED_CANONICAL_DECODER_EXACT_BYTES_RAW_VECTOR_ROUNDTRIP_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained. First kernel attempt passed. Parser/choice bit/actual modeled R2 multiplication compose a concrete Option success projection, with exact canonical acceptance, derived payload range/value, accepted32byte exact reserialization and canonical raw Scalar-vector recovery. Option models only documented success projection; native Choice/CtOption/private Scalar/compiler/primitive/full execution bindings remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
s=s.replace('actual modeled R2 decoder multiplication payload derives canonical raw/serialized input value','composed parser/finite choice/R2 multiplication derives exact32byte and canonical raw-vector codec roundtrips')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':997,'owned_modules':114,'first_attempt_passed':True})
