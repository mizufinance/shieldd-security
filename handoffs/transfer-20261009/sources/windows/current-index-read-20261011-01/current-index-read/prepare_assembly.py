"""Seal current-overlay index read and whole bound Ordinary duplicate refusal."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'assemble.py').exists()
source = (DIAG / 'transfer-ordinary-height-endpoint-20261011-01/assemble.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
source = source.replace('transfer-ordinary-height-source-20261011-01', 'transfer-ordinary-index-read-20261011-01')
source = source.replace('transfer-ordinary-height-checkpoint', 'transfer-ordinary-index-read-checkpoint')
source = source.replace('ordinary-height-endpoint', 'ordinary-index-read-endpoint')
replace("MODULE = 'TransferOrdinaryHeightSource01'", "MODULE = 'TransferOrdinaryIndexReadSource01'")
replace('assert len(fresh) == 5', 'assert len(fresh) == 7')
replace("assert pool['objects'] == 18 and len(pool['inherited_public_reports']) == 229", "assert pool['objects'] == 20 and len(pool['inherited_public_reports']) == 243")
replace("manager_endpoint = DIAG / 'transfer-ordinary-indexed-values-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-volume-height-keys-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-ordinary-indexed-values-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-volume-height-keys-endpoint01.tar.xz'")
replace('ccd2899c974ded96de44ff607a72a5fc8eea93df971bebecd717c0816265d24e', '0ed073e4bc92c301bda4449c38092e490ae399db16f010b87abf9cff4ab163b6')
replace("tar.extractfile('reports/fresh-2-complete-declarations.txt')", "tar.extractfile('reports/fresh-9-complete-declarations.txt')")
replace('assert len(manager_reports) == 2', 'assert len(manager_reports) == 9')
replace("'module': 'TransferOrdinaryIndexedValues01'", "'module': 'TransferVolumeHeightKeys01'")
replace('assert len(combined_reports) == 229', 'assert len(combined_reports) == 243')
replace('assert len(manager_selected) == 18', 'assert len(manager_selected) == 20')
replace("reference = {'indexed_values':", "reference = {'source_keys':")
replace("'imported_complete_reports': 2},", "'imported_complete_reports': 9},")
replace("'complete_owned_modules': 18, 'inherited_complete_reports': 229", "'complete_owned_modules': 20, 'inherited_complete_reports': 243")
replace('Exact eighteen-module closure through same-action indexed values, with all 229 inherited complete reports.',
    'Exact twenty-module closure through source ASCII volume/height keys and whole indexed success, with all 243 inherited complete reports.')
source = source.replace('two current-overlay height read/API definitions and three finite read/decode/V-frame/whole-indexed-height proofs', 'two current-overlay NV read/backend definitions and five finite read/duplicate/whole-delivery refusal proofs')
replace("add(stdout, 'reports/fresh-5-complete-declarations.txt'", "add(stdout, 'reports/fresh-7-complete-declarations.txt'")
source = source.replace('complete eighteen-module first import root', 'complete twenty-module first import root')
source = source.replace('verified 229 inherited reports', 'verified 243 inherited reports')
source = source.replace('WHOLE_ORDINARY_INDEXED_SUCCESS_DERIVES_ORIGINAL_PARENT_HEIGHT_FROM_CURRENT_OVERLAY_READ_QUALIFIED', 'CURRENT_OVERLAY_INDEX_READ_DERIVES_EXISTING_PARENT_ID_WHOLE_ORDINARY_DELIVERY_REFUSAL_QUALIFIED')
source = source.replace("'fresh_definition_audits': 2, 'fresh_theorem_audits': 3", "'fresh_definition_audits': 2, 'fresh_theorem_audits': 5")
source = source.replace("'fresh_complete_public_audits': 5", "'fresh_complete_public_audits': 7")
source = source.replace("'inherited_complete_public_audits': 229", "'inherited_complete_public_audits': 243")
start = source.index("    'scope': mapping['scope'] + ")
end = source.index("\ndump(ROOT / 'review.json', review)", start)
source = source[:start] + """    'scope': mapping['scope'] + ' Seven handwritten declarations qualified in the first guarded attempt. Read availability false cannot be counted as a semantic duplicate; the exact duplicate-error theorem explicitly derives it only when the actual modeled read is available and any value is present. Whole delivery refusal is unconditional on extraction/body outcomes and read availability, under explicit original-state height/decoder/ID and conversion observations. It does not assert raw error cache rollback or native Host fault reachability. No native, semantic control or durable-publication evidence.'}
""".rstrip() + source[end:]
source = source.replace("'fresh_audits': 5", "'fresh_audits': 7").replace("'inherited_audits': 229", "'inherited_audits': 243")
(ROOT / 'assemble.py').write_text(source)
print({'fresh_reports': 7, 'inherited_reports': 243, 'owned_modules': 20})
