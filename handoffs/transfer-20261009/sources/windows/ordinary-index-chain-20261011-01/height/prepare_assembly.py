"""Seal current-view height read and all-return V framing on exact closure."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'assemble.py').exists()
source = (DIAG / 'transfer-ordinary-indexed-values-endpoint-20261011-01/assemble.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
source = source.replace('transfer-ordinary-indexed-values-20261011-01', 'transfer-ordinary-height-source-20261011-01')
source = source.replace('transfer-ordinary-indexed-values-checkpoint', 'transfer-ordinary-height-checkpoint')
source = source.replace('ordinary-indexed-values-endpoint', 'ordinary-height-endpoint')
replace("MODULE = 'TransferOrdinaryIndexedValues01'", "MODULE = 'TransferOrdinaryHeightSource01'")
replace('assert len(fresh) == 2', 'assert len(fresh) == 5')
replace("assert pool['objects'] == 17 and len(pool['inherited_public_reports']) == 227", "assert pool['objects'] == 18 and len(pool['inherited_public_reports']) == 229")
replace("manager_endpoint = DIAG / 'transfer-ordinary-index-delivery-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-ordinary-indexed-values-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-ordinary-index-delivery-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-ordinary-indexed-values-endpoint01.tar.xz'")
replace('2b931c226179ab8f33f154b5e39c1873070b904162fcdfa39110706e7d44d908', 'ccd2899c974ded96de44ff607a72a5fc8eea93df971bebecd717c0816265d24e')
replace("tar.extractfile('reports/fresh-6-complete-declarations.txt')", "tar.extractfile('reports/fresh-2-complete-declarations.txt')")
replace('assert len(manager_reports) == 6', 'assert len(manager_reports) == 2')
replace("'module': 'TransferOrdinaryIndexDelivery01'", "'module': 'TransferOrdinaryIndexedValues01'")
replace('assert len(combined_reports) == 227', 'assert len(combined_reports) == 229')
replace('assert len(manager_selected) == 17', 'assert len(manager_selected) == 18')
replace("reference = {'index_delivery':", "reference = {'indexed_values':")
replace("'imported_complete_reports': 6},", "'imported_complete_reports': 2},")
replace("'complete_owned_modules': 17, 'inherited_complete_reports': 227", "'complete_owned_modules': 18, 'inherited_complete_reports': 229")
replace('Exact seventeen-module closure through whole Ordinary index delivery, with all 227 inherited complete reports.',
    'Exact eighteen-module closure through same-action indexed values, with all 229 inherited complete reports.')
source = source.replace('two finite same-action visible-index/volume-value and original-parent NV framing proofs', 'two current-overlay height read/API definitions and three finite read/decode/V-frame/whole-indexed-height proofs')
replace("add(stdout, 'reports/fresh-2-complete-declarations.txt'", "add(stdout, 'reports/fresh-5-complete-declarations.txt'")
source = source.replace('complete seventeen-module first import root', 'complete eighteen-module first import root')
source = source.replace('verified 227 inherited reports', 'verified 229 inherited reports')
source = source.replace('SAME_ACTION_WHOLE_ORDINARY_DELIVERY_DERIVES_EXACT_VISIBLE_INDEX_VALUES_AND_ORIGINAL_PARENT_NV_FRAME_QUALIFIED', 'WHOLE_ORDINARY_INDEXED_SUCCESS_DERIVES_ORIGINAL_PARENT_HEIGHT_FROM_CURRENT_OVERLAY_READ_QUALIFIED')
source = source.replace("'fresh_definition_audits': 0, 'fresh_theorem_audits': 2", "'fresh_definition_audits': 2, 'fresh_theorem_audits': 3")
source = source.replace("'fresh_complete_public_audits': 2", "'fresh_complete_public_audits': 5")
source = source.replace("'inherited_complete_public_audits': 227", "'inherited_complete_public_audits': 229")
start = source.index("    'scope': mapping['scope'] + ")
end = source.index("\ndump(ROOT / 'review.json', review)", start)
source = source[:start] + """    'scope': mapping['scope'] + ' All five handwritten declarations qualified on the first attempt. Actual runtime clock source reads get_proto at the block-height key and rejects missing values; current overlay and decoder are explicit executable model primitives, with real get_proto/u64/codecs and store correspondence still separate. Whole success derives parent bytes and the decoded height without a desired original value or stable-height callback premise. No native or durable-publication credit.'}
""".rstrip() + source[end:]
source = source.replace("'fresh_audits': 2", "'fresh_audits': 5").replace("'inherited_audits': 227", "'inherited_audits': 229")
(ROOT / 'assemble.py').write_text(source)
print({'fresh_reports': 5, 'inherited_reports': 229, 'owned_modules': 18})
