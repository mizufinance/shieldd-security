"""Seal canonical key constructor with finite symbolic inverse proof repairs."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-canonical-decoder-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
("CURRENT = DIAG / 'transfer-scalar-canonical-decoder-20261011-01'","CURRENT = DIAG / 'transfer-scalar-canonical-key-20261011-03'"),
("MODULE = 'TransferScalarCanonicalDecoder01'","MODULE = 'TransferScalarCanonicalKey01'"),
("assert pool['objects'] == 114 and len(pool['inherited_public_reports']) == 997","assert pool['objects'] == 115 and len(pool['inherited_public_reports']) == 1005"),
("manager_endpoint = DIAG / 'transfer-scalar-r2-payload-endpoint-20261011-01'","manager_endpoint = DIAG / 'transfer-scalar-canonical-decoder-endpoint-20261011-01'"),
("manager_archive = manager_endpoint / 'portable-windows-scalar-r2-payload-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-canonical-decoder-endpoint01.tar.xz'"),
('1c4931d770ee5aa27cd9317703a7064162900a53b4b3a26f4330ea799893319a','13e2553cf8840a7a6d6d89acfc98162a6433ea896e1bd803359b1a76edcb3ec7'),
("tar.extractfile('reports/fresh-7-complete-declarations.txt')","tar.extractfile('reports/fresh-8-complete-declarations.txt')"),
('assert len(manager_reports) == 7','assert len(manager_reports) == 8'),
("'module': 'TransferScalarR2Payload01'","'module': 'TransferScalarCanonicalDecoder01'"),
('assert len(combined_reports) == 997','assert len(combined_reports) == 1005'),
('assert len(manager_selected) == 114','assert len(manager_selected) == 115'),
("reference = {'scalar_r2_payload':","reference = {'scalar_canonical_decoder':"),
("'imported_complete_reports': 7","'imported_complete_reports': 8"),
("'complete_owned_modules': 114, 'inherited_complete_reports': 997","'complete_owned_modules': 115, 'inherited_complete_reports': 1005"),
("'fresh_definition_audits': 3","'fresh_definition_audits': 2"),
("'fresh_theorem_audits': 5","'fresh_theorem_audits': 6"),
("'inherited_complete_public_audits': 997","'inherited_complete_public_audits': 1005"),
("'rejected_attempts': 0","'rejected_attempts': 2"),
("archive = ROOT / 'portable-windows-scalar-canonical-decoder-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-canonical-key-endpoint01.tar.xz'")]:replace(a,b)
replace("'fresh_audits': 8, 'inherited_audits': 997","'fresh_audits': 8, 'inherited_audits': 1005",2)
s=s.replace('transfer-scalar-canonical-decoder-checkpoint-20261011-01','transfer-scalar-canonical-key-checkpoint-20261011-03').replace('transfer-scalar-canonical-decoder-endpoint-v1','transfer-scalar-canonical-key-endpoint-v1').replace('one-hundred-fourteen-module','one-hundred-fifteen-module').replace('997 original inherited','1005 original inherited').replace('verified 997 inherited','verified 1005 inherited')
s=s.replace('SOURCE_CONSTRUCTED_CANONICAL_DECODER_EXACT_BYTES_RAW_VECTOR_ROUNDTRIP_QUALIFIED','SOURCE_CANONICAL_KEY_CONSTRUCTOR_GLOBAL_FIELD_VECTOR_INVERSE_QUALIFIED')
needle="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"
replace(needle,needle+"\nfor attempt in [1,2]:\n    failed=DIAG/('transfer-scalar-canonical-key-20261011-'+str(attempt).zfill(2))\n    for name in ['prepare_recipe.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','handwritten/TransferScalarCanonicalKey01.lean','project/ShielddSecurity/TransferScalarCanonicalKey01.lean','runs/01-TransferScalarCanonicalKey01/stdout.txt']:\n        assert pin(failed/name) in plan['pins']\n        add(failed/name,'unselected/'+str(attempt).zfill(2)+'/'+name,'complete original finite-heartbeat failure retained; zero credit')")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Eight complete full type/axiom reports retained. Fresh03 after two finite-heartbeat failures01/02, all twenty raw files retained/pinned with zero credit. Equality chain/local serializer irreducibility change elaboration only; no changed contracts/definitions/axioms/limits. Construct canonical field through LE/actual modeled R2 decoder; derive source key, exact bytes, actual modeled decode success and full canonical raw-vector inverse/injectivity. Native private Scalar/primitive/compiler/Choice/CtOption/containers/full trace remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
s=s.replace('composed parser/finite choice/R2 multiplication derives exact32byte and canonical raw-vector codec roundtrips','canonical natural field key constructor via actual modeled decoder derives source key/raw-vector inverse')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':8,'inherited_reports':1005,'owned_modules':115,'preserved_failures':2})
