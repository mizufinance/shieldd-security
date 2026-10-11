"""Seal source-derived pending field codec after symbolic kernel-cost repair."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-symbolic-field-map-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
("CURRENT = DIAG / 'transfer-symbolic-field-map-20261011-01'","CURRENT = DIAG / 'transfer-canonical-word-pending-20261011-03'"),
("MODULE = 'TransferSymbolicFieldMap01'","MODULE = 'TransferCanonicalWordPending01'"),
('assert len(fresh) == 2','assert len(fresh) == 8'),
("assert pool['objects'] == 116 and len(pool['inherited_public_reports']) == 1013","assert pool['objects'] == 117 and len(pool['inherited_public_reports']) == 1015"),
("manager_endpoint = DIAG / 'transfer-scalar-canonical-key-endpoint-20261011-03'","manager_endpoint = DIAG / 'transfer-symbolic-field-map-endpoint-20261011-01'"),
("manager_archive = manager_endpoint / 'portable-windows-scalar-canonical-key-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-symbolic-field-map-endpoint01.tar.xz'"),
('a2993c3646b494a91bcaabf85d398be8426439c8fdb8d6afa06380d4fe866ca6','92bcf352e2cc925bcb60911501d9a6ccfcb7bf104434c44098cb9dbc6e400a9e'),
("tar.extractfile('reports/fresh-8-complete-declarations.txt')","tar.extractfile('reports/fresh-2-complete-declarations.txt')"),
('assert len(manager_reports) == 8','assert len(manager_reports) == 2'),
("'module': 'TransferScalarCanonicalKey01'","'module': 'TransferSymbolicFieldMap01'"),
('assert len(combined_reports) == 1013','assert len(combined_reports) == 1015'),
('assert len(manager_selected) == 116','assert len(manager_selected) == 117'),
("reference = {'scalar_canonical_key':","reference = {'symbolic_field_map':"),
("'imported_complete_reports': 8","'imported_complete_reports': 2"),
("'complete_owned_modules': 116, 'inherited_complete_reports': 1013","'complete_owned_modules': 117, 'inherited_complete_reports': 1015"),
("'fresh_definition_audits': 0","'fresh_definition_audits': 3"),
("'fresh_structure_audits': 0","'fresh_structure_audits': 1"),
("'fresh_theorem_audits': 2","'fresh_theorem_audits': 4"),
("'fresh_complete_public_audits': 2","'fresh_complete_public_audits': 8"),
("'inherited_complete_public_audits': 1013","'inherited_complete_public_audits': 1015"),
("'rejected_attempts': 0","'rejected_attempts': 2"),
("archive = ROOT / 'portable-windows-symbolic-field-map-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-canonical-word-pending-endpoint01.tar.xz'"),
("add(stdout, 'reports/fresh-2-complete-declarations.txt'","add(stdout, 'reports/fresh-8-complete-declarations.txt'")]:replace(a,b)
replace("'fresh_audits': 2, 'inherited_audits': 1013","'fresh_audits': 8, 'inherited_audits': 1015",2)
s=s.replace('transfer-symbolic-field-map-checkpoint-20261011-01','transfer-canonical-word-pending-checkpoint-20261011-03').replace('transfer-symbolic-field-map-endpoint-v1','transfer-canonical-word-pending-endpoint-v1').replace('one-hundred-sixteen-module','one-hundred-seventeen-module').replace('1013 original inherited','1015 original inherited').replace('verified 1013 inherited','verified 1015 inherited')
s=s.replace('SYMBOLIC_FINITE_FIELD_LIST_PROJECTION_ROUNDTRIP_LEMMAS_QUALIFIED','SOURCE_CONSTRUCTED_CANONICAL_WORD_PENDING_FINITE_CODEC_QUALIFIED')
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained. Fresh03 after concrete kernel-memory failures01/02; twenty complete original raw files retained/pinned with zero credit. Small symbolic mapping lemma instantiation preserves eight contracts and current bounds/guards. Each finite field constructed by actual modeled LE/parser/choice/R2 decoder; canonical supported enum fields restore exactly, yielding bounded coherent current Pending codec. Finite seen member-list representation only; native imbl/private Scalar/Any/Clone/primitive/compiler/Choice/CtOption/full trace/ownership remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
s=s.replace('symbolic polymorphic mapping lemmas required by live typed pending field codec','source-derived canonical raw Scalar-word fields in concrete finite pending enum/list codec')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':1015,'owned_modules':117,'preserved_failures':2})
