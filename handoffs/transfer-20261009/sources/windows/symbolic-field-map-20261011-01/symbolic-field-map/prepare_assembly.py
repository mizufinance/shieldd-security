"""Seal tiny reusable mapping proof and retain failed concrete kernel histories."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-canonical-key-endpoint-20261011-03/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
("CURRENT = DIAG / 'transfer-scalar-canonical-key-20261011-03'","CURRENT = DIAG / 'transfer-symbolic-field-map-20261011-01'"),
("MODULE = 'TransferScalarCanonicalKey01'","MODULE = 'TransferSymbolicFieldMap01'"),
('assert len(fresh) == 8','assert len(fresh) == 2'),
("assert pool['objects'] == 115 and len(pool['inherited_public_reports']) == 1005","assert pool['objects'] == 116 and len(pool['inherited_public_reports']) == 1013"),
("manager_endpoint = DIAG / 'transfer-scalar-canonical-decoder-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-scalar-canonical-key-endpoint-20261011-03'"),
("manager_archive = manager_endpoint / 'portable-windows-scalar-canonical-decoder-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-canonical-key-endpoint01.tar.xz'"),
('13e2553cf8840a7a6d6d89acfc98162a6433ea896e1bd803359b1a76edcb3ec7','a2993c3646b494a91bcaabf85d398be8426439c8fdb8d6afa06380d4fe866ca6'),
("'module': 'TransferScalarCanonicalDecoder01'","'module': 'TransferScalarCanonicalKey01'"),
('assert len(combined_reports) == 1005','assert len(combined_reports) == 1013'),
('assert len(manager_selected) == 115','assert len(manager_selected) == 116'),
("reference = {'scalar_canonical_decoder':","reference = {'scalar_canonical_key':"),
("'complete_owned_modules': 115, 'inherited_complete_reports': 1005","'complete_owned_modules': 116, 'inherited_complete_reports': 1013"),
("'fresh_definition_audits': 2","'fresh_definition_audits': 0"),
("'fresh_theorem_audits': 6","'fresh_theorem_audits': 2"),
("'fresh_complete_public_audits': 8","'fresh_complete_public_audits': 2"),
("'inherited_complete_public_audits': 1005","'inherited_complete_public_audits': 1013"),
("'rejected_attempts': 2","'rejected_attempts': 0"),
("archive = ROOT / 'portable-windows-scalar-canonical-key-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-symbolic-field-map-endpoint01.tar.xz'")]:replace(a,b)
replace("'fresh_audits': 8, 'inherited_audits': 1005","'fresh_audits': 2, 'inherited_audits': 1013",2)
replace("add(stdout, 'reports/fresh-8-complete-declarations.txt'","add(stdout, 'reports/fresh-2-complete-declarations.txt'")
s=s.replace('transfer-scalar-canonical-key-checkpoint-20261011-03','transfer-symbolic-field-map-checkpoint-20261011-01').replace('transfer-scalar-canonical-key-endpoint-v1','transfer-symbolic-field-map-endpoint-v1').replace('one-hundred-fifteen-module','one-hundred-sixteen-module').replace('1005 original inherited','1013 original inherited').replace('verified 1005 inherited','verified 1013 inherited')
s=s.replace('SOURCE_CANONICAL_KEY_CONSTRUCTOR_GLOBAL_FIELD_VECTOR_INVERSE_QUALIFIED','SYMBOLIC_FINITE_FIELD_LIST_PROJECTION_ROUNDTRIP_LEMMAS_QUALIFIED')
replace("failed=DIAG/('transfer-scalar-canonical-key-20261011-'+str(attempt).zfill(2))","failed=DIAG/('transfer-canonical-word-pending-20261011-'+str(attempt).zfill(2))")
s=s.replace('handwritten/TransferScalarCanonicalKey01.lean','handwritten/TransferCanonicalWordPending01.lean').replace('project/ShielddSecurity/TransferScalarCanonicalKey01.lean','project/ShielddSecurity/TransferCanonicalWordPending01.lean').replace('runs/01-TransferScalarCanonicalKey01/stdout.txt','runs/01-TransferCanonicalWordPending01/stdout.txt').replace('complete original finite-heartbeat failure retained; zero credit','complete original concrete kernel-memory failure retained; zero credit')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Two complete full type/axiom reports retained. First kernel attempt passed. Polymorphic encoder/projector/ref mapping yields exact list projection or list inverse from pointwise premise; this premise is explicit here and supplied by proved source field constructor in the concrete codec. Both prior concrete WordPending failures retained in twenty original raw files; zero credit. Needed only by live pending field claim. No native/compiler/trace credit and no ancestor replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
s=s.replace('canonical natural field key constructor via actual modeled decoder derives source key/raw-vector inverse','symbolic polymorphic mapping lemmas required by live typed pending field codec')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':2,'inherited_reports':1013,'owned_modules':116,'first_attempt_passed':True})
