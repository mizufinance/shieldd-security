"""Seal complete bound Ordinary join with exact union of two parent closures."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'assemble.py').exists()
source = (DIAG / 'transfer-ordinary-storage-endpoint-20261011-01/assemble.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
source = source.replace('transfer-ordinary-storage-source-20261011-02', 'transfer-bound-ordinary-source-20261011-02')
source = source.replace('transfer-ordinary-storage-checkpoint', 'transfer-bound-ordinary-checkpoint')
source = source.replace('ordinary-storage-endpoint', 'bound-ordinary-endpoint')
replace("MODULE = 'TransferOrdinaryStorageSource01'", "MODULE = 'TransferBoundOrdinarySource01'")
replace("assert pool['objects'] == 9 and len(pool['inherited_public_reports']) == 126", "assert pool['objects'] == 12 and len(pool['inherited_public_reports']) == 162")
replace("manager_endpoint = DIAG / 'transfer-current-volume-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-ordinary-storage-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-current-volume-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-ordinary-storage-endpoint01.tar.xz'")
replace('7c344cdaed324ac7e37fdc253deeb5e259a17f484eb27febdb997867962058b5', '428a659fe44b3dd53be178bba4b3f50d2893616646bf67905ffab997475c2e53')
replace("tar.extractfile('reports/fresh-9-complete-declarations.txt')", "tar.extractfile('reports/fresh-12-complete-declarations.txt')")
replace('assert len(manager_reports) == 9', 'assert len(manager_reports) == 12')
replace("assert {**manager_pool['inherited_public_reports'], **manager_reports} == pool['inherited_public_reports']", "combined_reports = {**manager_pool['inherited_public_reports'], **manager_reports}")
replace("'module': 'TransferCurrentVolumeSource01'", "'module': 'TransferOrdinaryStorageSource01'")
replace("for selected in pool['selected']:", """equality_endpoint = DIAG / 'transfer-verification-equality-endpoint-20261011-01'
equality_archive = equality_endpoint / 'portable-windows-verification-equality-endpoint01.tar.xz'
assert pin(equality_archive)['sha256'] == '13a3e1d2302d436a80e88221274b11b2c2469f652b25feefa381cdc4b3c19c77'
with tarfile.open(equality_archive, 'r:xz') as tar:
    equality_review = json.loads(tar.extractfile('review.json').read())
    equality_reference = json.loads(tar.extractfile('context/inherited-reference.json').read())
    equality_pool = json.loads(tar.extractfile('context/owned-composition-review.json').read())
    equality_plan = json.loads(tar.extractfile('qualified/plan.json').read())
    equality_events = [json.loads(s) for s in tar.extractfile('qualified/events.jsonl').read().decode().splitlines()]
    equality_reports = m.audit(tar.extractfile('reports/fresh-13-complete-declarations.txt').read().decode(), equality_plan['targets'][0]['audit_names'])
assert len(equality_reports) == 13 and equality_reports == equality_review['fresh_audits'] == equality_events[-1]['result']['audits']
for name, report in {**equality_pool['inherited_public_reports'], **equality_reports}.items():
    assert name not in combined_reports or combined_reports[name] == report
    combined_reports[name] = report
assert len(combined_reports) == 162 and combined_reports == pool['inherited_public_reports']
for row in equality_pool['selected'] + [{'module': 'TransferVerificationEqualitySource01',
    'source': equality_plan['targets'][0]['source'], 'object': equality_events[-1]['result']['objects'][0]}]:
    original = next((r for r in manager_selected if r['module'] == row['module']), None)
    if original:
        assert original['source'] == row['source'] and original['object'] == row['object']
    else:
        manager_selected.append(row)
assert len(manager_selected) == 12
for selected in pool['selected']:""")
replace('    carriers = [pin(manager_archive)]', '    carriers = [pin(manager_archive), pin(equality_archive)]')
replace('    collect_archive_refs(manager_reference)', '    collect_archive_refs(manager_reference)\n    collect_archive_refs(equality_reference)')
replace("assert manager_reference['ancestors']['ancestors']['ancestors']['core_floor']['original'] == plan['external_floor']", "assert manager_reference['ancestors']['ancestors']['ancestors']['ancestors']['core_floor']['original'] == plan['external_floor']")
replace("reference = {'current_volume':", "reference = {'ordinary_storage':")
source = source.replace('PARENT_REVIEW_ACCEPTED_AND_PUBLISHED_b124dc50bfc6f18b75557c70e61799cab17a90a8', 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE')
source = source.replace("'imported_complete_reports': 9", "'imported_complete_reports': 12")
replace("    'ancestors': manager_reference, 'complete_owned_modules': 9, 'inherited_complete_reports': 126,", """    'equality': {'archive': pin(equality_archive), 'manifest': pin(equality_endpoint / 'manifest.json'),
        'status': 'PARENT_REVIEW_ACCEPTED_AND_PUBLISHED_22a1ab0491ad7e744aca9cfa8e1eca65b54c7e61', 'imported_complete_reports': 13,
        'ancestors': equality_reference},
    'ancestors': manager_reference, 'complete_owned_modules': 12, 'inherited_complete_reports': 162,""")
replace('Exact cache/raw/vector/batch/raw-effect/manager/SCT/framing/current-volume closure; capability and equality modules are not imported or replayed here.',
    'Exact twelve-module union of Ordinary storage and capability/Verification equality; shared five-module raw sources/objects and 84 reports counted once. No ancestors replayed here.')
source = source.replace('three both-callback executable definitions and nine finite Ordinary cache/read/write proofs', 'two bound body/delivery definitions and ten finite source/equality/cache/read/write/refusal proofs')
source = source.replace('complete nine-module first import root', 'complete twelve-module first import root')
source = source.replace('verified 126 inherited reports', 'verified 162 inherited reports')
source = source.replace('transfer-ordinary-storage-source-20261011-01', 'transfer-bound-ordinary-source-20261011-01')
source = source.replace('BOTH_SCT_CALLBACKS_DERIVE_ALL_RETURN_ORDINARY_CACHE_FRAMES_AND_SUCCESS_MARKERS_QUALIFIED', 'WHOLE_ITEM_REEXTRACTION_DERIVES_ORDINARY_MARKERS_AND_ENCLOSING_DELIVERY_REFUSAL_QUALIFIED')
source = source.replace("'fresh_definition_audits': 3, 'fresh_theorem_audits': 9", "'fresh_definition_audits': 2, 'fresh_theorem_audits': 10")
source = source.replace("'inherited_complete_public_audits': 126", "'inherited_complete_public_audits': 162")
start = source.index("    'scope': mapping['scope'] + ")
end = source.index("\ndump(ROOT / 'review.json', review)", start)
source = source[:start] + """    'scope': mapping['scope'] + ' All two program definitions and ten theorem contracts are unchanged from rejected01; only one proof rewrite now exposes executeBound before the existing dispatch lemma. Same Ordinary context/action/Item appears in extraction, comparison and raw projections. Success inversion derives the compared Item and marker results from the whole modeled body. Initial existing entry refusal needs no desired match, successful reshape, spent read or parent rollback premise. Original compiler rejection receives full zero credit; no native control or certificate.'}
""".rstrip() + source[end:]
source = source.replace("'inherited_audits': 126", "'inherited_audits': 162")
(ROOT / 'assemble.py').write_text(source)
print({'fresh_reports': 12, 'inherited_reports': 162, 'owned_modules': 12})
