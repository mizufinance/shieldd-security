"""Seal both-callback Ordinary source result and exact current-overlay inheritance."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'assemble.py').exists()
source = (DIAG / 'transfer-current-volume-endpoint-20261011-01/assemble.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
source = source.replace('transfer-current-volume-source-20261011-02', 'transfer-ordinary-storage-source-20261011-02')
source = source.replace('transfer-current-volume-checkpoint', 'transfer-ordinary-storage-checkpoint')
source = source.replace('current-volume-endpoint', 'ordinary-storage-endpoint')
replace("MODULE = 'TransferCurrentVolumeSource01'", "MODULE = 'TransferOrdinaryStorageSource01'")
replace('assert len(fresh) == 9', 'assert len(fresh) == 12')
replace("assert pool['objects'] == 8 and len(pool['inherited_public_reports']) == 117", "assert pool['objects'] == 9 and len(pool['inherited_public_reports']) == 126")
replace("manager_endpoint = DIAG / 'transfer-raw-source-frames-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-current-volume-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-raw-source-frames-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-current-volume-endpoint01.tar.xz'")
replace('3623e7b32a7fb61bae9bfb85408e9686d0901361d3de6b16fc36b1220c9a32af', '7c344cdaed324ac7e37fdc253deeb5e259a17f484eb27febdb997867962058b5')
replace("tar.extractfile('reports/fresh-7-complete-declarations.txt')", "tar.extractfile('reports/fresh-9-complete-declarations.txt')")
replace('assert len(manager_reports) == 7', 'assert len(manager_reports) == 9')
replace("'module': 'TransferRawSourceFrames01'", "'module': 'TransferCurrentVolumeSource01'")
start = source.index("    if selected['module'] == 'TransferRawSourceFrames01':")
end = source.index("reference = {'framing':", start)
source = source[:start] + """    carriers = [pin(manager_archive)]
    def collect_archive_refs(value):
        if isinstance(value, dict):
            if 'archive' in value and isinstance(value['archive'], dict) and 'path' in value['archive']:
                carriers.append(value['archive'])
            for nested in value.values():
                collect_archive_refs(nested)
        elif isinstance(value, list):
            for nested in value:
                collect_archive_refs(nested)
    collect_archive_refs(manager_reference)
    member = 'source/ShielddSecurity/' + selected['module'] + '.lean'
    found = False
    for carrier in {r['path']: r for r in carriers}.values():
        assert pin(carrier['path']) == carrier
        with tarfile.open(carrier['path'], 'r:xz') as tar:
            if member in tar.getnames():
                assert tar.extractfile(member).read() == Path(selected['source']['path']).read_bytes()
                found = True
                break
    assert found, selected['module']
assert manager_reference['ancestors']['ancestors']['ancestors']['core_floor']['original'] == plan['external_floor']
""" + source[end:]
replace("reference = {'framing':", "reference = {'current_volume':")
source = source.replace('PARENT_REVIEW_ACCEPTED_AND_PUBLISHED_f6b0a8c5e1df4d2188d1f5e6ae31e9b3973ce822', 'PARENT_REVIEW_ACCEPTED_AND_PUBLISHED_b124dc50bfc6f18b75557c70e61799cab17a90a8')
source = source.replace("'imported_complete_reports': 7", "'imported_complete_reports': 9")
source = source.replace("'complete_owned_modules': 8", "'complete_owned_modules': 9")
source = source.replace("'inherited_complete_reports': 117", "'inherited_complete_reports': 126")
source = source.replace('Exact cache/raw/vector/batch/raw-effect/manager/SCT/framing closure;', 'Exact cache/raw/vector/batch/raw-effect/manager/SCT/framing/current-volume closure;')
source = source.replace('four current-overlay executable definitions and five finite source-derived refusal proofs', 'three both-callback executable definitions and nine finite Ordinary cache/read/write proofs')
source = source.replace("reports/fresh-9-complete-declarations.txt', 'all raw", "reports/fresh-12-complete-declarations.txt', 'all raw")
source = source.replace('complete eight-module first import root', 'complete nine-module first import root')
source = source.replace('verified 117 inherited reports', 'verified 126 inherited reports')
source = source.replace('transfer-current-volume-source-20261011-01', 'transfer-ordinary-storage-source-20261011-01')
source = source.replace('exact pinned current volume get_raw and layered cache source; semantic interfaces explicit', 'exact pinned Ordinary payload/SCT/current-volume source; semantic interfaces explicit')
source = source.replace('SOURCE_DERIVED_CURRENT_OVERLAY_ORDINARY_REFUSAL_AND_DELIVERY_PRESERVATION_QUALIFIED', 'BOTH_SCT_CALLBACKS_DERIVE_ALL_RETURN_ORDINARY_CACHE_FRAMES_AND_SUCCESS_MARKERS_QUALIFIED')
source = source.replace("'fresh_definition_audits': 4, 'fresh_theorem_audits': 5", "'fresh_definition_audits': 3, 'fresh_theorem_audits': 9")
source = source.replace("'fresh_complete_public_audits': 9", "'fresh_complete_public_audits': 12")
source = source.replace("'inherited_complete_public_audits': 117", "'inherited_complete_public_audits': 126")
start = source.index("    'pre_admission_refused_cli':")
end = source.index("\ndump(ROOT / 'review.json', review)", start)
source = source[:start] + """    'scope': mapping['scope'] + ' All three executable definitions and nine theorem contracts are unchanged from the failed attempt; successor proof annotations make the two reshape V/NV observations syntactically available at the installed backend alias and discharge a simplified True. Both markers persist after returned volume SCT/pending callback errors in this immutable model. Raw objects/events may remain altered. Successfully loaded immutable trees, actual getter panic, Clone/COW, key/value/event/source projections, tree and reader semantics, block finalization and durability remain explicit interfaces. Failed predecessor full zero credit.'}
""".rstrip() + source[end:]
source = source.replace("'fresh_audits': 9", "'fresh_audits': 12").replace("'inherited_audits': 117", "'inherited_audits': 126")
(ROOT / 'assemble.py').write_text(source)
print({'fresh_reports': 12, 'inherited_reports': 126, 'owned_modules': 9})
