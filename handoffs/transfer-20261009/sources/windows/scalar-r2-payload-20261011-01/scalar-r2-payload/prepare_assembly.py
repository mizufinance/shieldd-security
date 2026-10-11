"""Seal first-pass exact modeled R2 decoder payload and original constant shape."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-scalar-wide-reduction-endpoint-20261011-02/assemble.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a));s=s.replace(a,b)
for a,b in [
("CURRENT = DIAG / 'transfer-scalar-wide-reduction-20261011-02'","CURRENT = DIAG / 'transfer-scalar-r2-payload-20261011-01'"),
("MODULE = 'TransferScalarWideReduction01'","MODULE = 'TransferScalarR2Payload01'"),
('assert len(fresh) == 8','assert len(fresh) == 7'),
("assert pool['objects'] == 112 and len(pool['inherited_public_reports']) == 982","assert pool['objects'] == 113 and len(pool['inherited_public_reports']) == 990"),
("manager_endpoint = DIAG / 'transfer-scalar-wide-walk-endpoint-20261011-02'","manager_endpoint = DIAG / 'transfer-scalar-wide-reduction-endpoint-20261011-02'"),
("manager_archive = manager_endpoint / 'portable-windows-scalar-wide-walk-endpoint01.tar.xz'","manager_archive = manager_endpoint / 'portable-windows-scalar-wide-reduction-endpoint01.tar.xz'"),
('84b545606b983add064733468051e4462b6a8e82fed6d24b31e9c91cbbfdffdb','326fdd77a0ff7f6c84902fd2fff7a74e8abffefde270f97b2a80cba545339ac4'),
("tar.extractfile('reports/fresh-7-complete-declarations.txt')","tar.extractfile('reports/fresh-8-complete-declarations.txt')"),
('assert len(manager_reports) == 7','assert len(manager_reports) == 8'),
("'module': 'TransferScalarWideWalk01'","'module': 'TransferScalarWideReduction01'"),
('assert len(combined_reports) == 982','assert len(combined_reports) == 990'),
('assert len(manager_selected) == 112','assert len(manager_selected) == 113'),
("reference = {'scalar_wide_walk':","reference = {'scalar_wide_reduction':"),
("'imported_complete_reports': 7","'imported_complete_reports': 8"),
("'complete_owned_modules': 112, 'inherited_complete_reports': 982","'complete_owned_modules': 113, 'inherited_complete_reports': 990"),
("'fresh_theorem_audits': 6","'fresh_theorem_audits': 5"),
("'fresh_complete_public_audits': 8","'fresh_complete_public_audits': 7"),
("'inherited_complete_public_audits': 982","'inherited_complete_public_audits': 990"),
("add(stdout, 'reports/fresh-8-complete-declarations.txt'","add(stdout, 'reports/fresh-7-complete-declarations.txt'"),
("'rejected_attempts': 1","'rejected_attempts': 0")]:replace(a,b)
replace("'fresh_audits': 8, 'inherited_audits': 982","'fresh_audits': 7, 'inherited_audits': 990",2)
s=s.replace('transfer-scalar-wide-reduction-checkpoint-20261011-02','transfer-scalar-r2-payload-checkpoint-20261011-01')
replace("archive = ROOT / 'portable-windows-scalar-wide-reduction-endpoint01.tar.xz'","archive = ROOT / 'portable-windows-scalar-r2-payload-endpoint01.tar.xz'")
s=s.replace('transfer-scalar-wide-reduction-endpoint-v1','transfer-scalar-r2-payload-endpoint-v1').replace('one-hundred-twelve-module','one-hundred-thirteen-module').replace('982 original inherited','990 original inherited').replace('verified 982 inherited','verified 990 inherited')
s=s.replace('SOURCE_FULL_WIDE_REDUCTION_ZERO_DISCARDED_CARRY_CANONICAL_PRODUCT_QUALIFIED','SOURCE_EXACT_R2_MODELED_DECODER_PAYLOAD_QUALIFIED')
start=s.index("failed=DIAG/'transfer-scalar-wide-reduction-20261011-01'");end=s.index("row = mapping['wide_product_source_shape']",start);s=s[:start]+s[end:]
needle="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"
replace(needle,needle+"\nrow = mapping['r2_decoder_payload_source_shape']\nassert pin(row['path']) == row and row in plan['pins']\nadd(row['path'], 'context/r2-decoder-payload-shape.json', 'exact pinned R2 literal and decoder multiplication/CtOption static source association; native binding separate')")
start=s.index("    'scope': mapping['scope'] + ");end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"    'scope': mapping['scope'] + ' Seven complete full type/axiom reports retained. First kernel attempt passed. Pinned R2 constant exact value/range/inverse relation is kernel-certified. Payload constructed by actual modeled MAC/ADC/wide reduction/subtract schedule derives canonical raw Montgomery value and serializer raw-mod-p value; no target payload supplied. Native private Scalar/compiler/primitive/Choice/CtOption/full trace remain explicit. No ancestor/native replay. Full Transfer OPEN; zero native/control/certification credit.'}"+s[end:]
s=s.replace('full modeled wide reduction derives zero discarded carry/canonical range/exact product relation','actual modeled R2 decoder multiplication payload derives canonical raw/serialized input value')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':990,'owned_modules':113,'first_attempt_passed':True})
