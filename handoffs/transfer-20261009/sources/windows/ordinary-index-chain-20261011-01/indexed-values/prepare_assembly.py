"""Seal same-action visible values and original-parent NV frame without replay."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'assemble.py').exists()
source = (DIAG / 'transfer-ordinary-index-delivery-endpoint-20261011-01/assemble.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
source = source.replace('transfer-ordinary-index-delivery-20261011-02', 'transfer-ordinary-indexed-values-20261011-01')
source = source.replace('transfer-ordinary-index-delivery-checkpoint', 'transfer-ordinary-indexed-values-checkpoint')
source = source.replace('ordinary-index-delivery-endpoint', 'ordinary-indexed-values-endpoint')
replace("MODULE = 'TransferOrdinaryIndexDelivery01'", "MODULE = 'TransferOrdinaryIndexedValues01'")
replace('assert len(fresh) == 6', 'assert len(fresh) == 2')
replace("assert pool['objects'] == 16 and len(pool['inherited_public_reports']) == 221", "assert pool['objects'] == 17 and len(pool['inherited_public_reports']) == 227")
replace("manager_endpoint = DIAG / 'transfer-bound-ordinary-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-ordinary-index-delivery-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-bound-ordinary-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-ordinary-index-delivery-endpoint01.tar.xz'")
replace('316f55d8f00be6988ed16c0c1e74af460372d73cd5c35e60d25e671d69a7af7d', '2b931c226179ab8f33f154b5e39c1873070b904162fcdfa39110706e7d44d908')
replace("tar.extractfile('reports/fresh-12-complete-declarations.txt')", "tar.extractfile('reports/fresh-6-complete-declarations.txt')")
replace('assert len(manager_reports) == 12', 'assert len(manager_reports) == 6')
replace("'module': 'TransferBoundOrdinarySource01'", "'module': 'TransferOrdinaryIndexDelivery01'")
start = source.index("inspection_endpoint = DIAG / 'transfer-index-inspection-endpoint-20261011-01'")
end = source.index("for selected in pool['selected']:", start)
source = source[:start] + "assert len(combined_reports) == 227 and combined_reports == pool['inherited_public_reports']\nassert len(manager_selected) == 17\n" + source[end:]
replace('    carriers = [pin(manager_archive), pin(inspection_archive)]', '    carriers = [pin(manager_archive)]')
replace('    collect_archive_refs(inspection_reference)\n', '')
replace("reference = {'bound_ordinary':", "reference = {'index_delivery':")
replace("'imported_complete_reports': 12},", "'imported_complete_reports': 6},")
start = source.index("    'inspection': {'archive': pin(inspection_archive)")
end = source.index("    'ancestors': manager_reference", start)
source = source[:start] + source[end:]
replace("'complete_owned_modules': 16, 'inherited_complete_reports': 221", "'complete_owned_modules': 17, 'inherited_complete_reports': 227")
replace('Exact sixteen-module union of bound Ordinary body and concrete index inspection; shared StateDelta/Raw sources/objects and 28 reports counted once. No ancestors replayed here.',
    'Exact seventeen-module closure through whole Ordinary index delivery, with all 227 inherited complete reports. No ancestors replayed here.')
replace("for name in ['prepare.py', 'prepare_successor.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:", "for name in ['prepare.py', 'prepare_recipe.py', 'execute_bounded.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl']:")
source = source.replace('one body/index API definition and five finite whole-call success/inspection/frame/marker proofs', 'two finite same-action visible-index/volume-value and original-parent NV framing proofs')
replace("add(stdout, 'reports/fresh-6-complete-declarations.txt'", "add(stdout, 'reports/fresh-2-complete-declarations.txt'")
source = source.replace('complete sixteen-module first import root', 'complete seventeen-module first import root')
source = source.replace('verified 221 inherited reports', 'verified 227 inherited reports')
start = source.index("old = DIAG / 'transfer-ordinary-index-delivery-20261011-01'")
end = source.index("for name in ['preservation_check.py', 'preservation.json']:", start)
source = source[:start] + source[end:]
source = source.replace('WHOLE_ORDINARY_PER_TRANSACTION_DELIVERY_DERIVES_BODY_MARKERS_AND_CONCRETE_INDEX_WRITES_QUALIFIED', 'SAME_ACTION_WHOLE_ORDINARY_DELIVERY_DERIVES_EXACT_VISIBLE_INDEX_VALUES_AND_ORIGINAL_PARENT_NV_FRAME_QUALIFIED')
source = source.replace("'fresh_definition_audits': 1, 'fresh_theorem_audits': 5", "'fresh_definition_audits': 0, 'fresh_theorem_audits': 2")
source = source.replace("'fresh_complete_public_audits': 6", "'fresh_complete_public_audits': 2")
source = source.replace("'inherited_complete_public_audits': 221", "'inherited_complete_public_audits': 227")
source = source.replace("'rejected_attempts': 1", "'rejected_attempts': 0")
start = source.index("    'scope': mapping['scope'] + ")
end = source.index("\ndump(ROOT / 'review.json', review)", start)
source = source[:start] + """    'scope': mapping['scope'] + ' Both handwritten theorems qualified on first attempt. A single action is shared by the extractor, raw projections and index conversion. Representation-preserving projection is explicit, not a claim of hash injectivity. Original parent NV preservation follows executable body and index primitives. This adds no native, block seal or durable-publication evidence.'}
""".rstrip() + source[end:]
source = source.replace("'fresh_audits': 6", "'fresh_audits': 2").replace("'inherited_audits': 221", "'inherited_audits': 227")
(ROOT / 'assemble.py').write_text(source)
print({'fresh_reports': 2, 'inherited_reports': 227, 'owned_modules': 17})
