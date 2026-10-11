"""Seal whole per-transaction source join with complete bound/index inheritance."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'assemble.py').exists()
source = (DIAG / 'transfer-bound-ordinary-endpoint-20261011-01/assemble.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
source = source.replace('transfer-bound-ordinary-source-20261011-02', 'transfer-ordinary-index-delivery-20261011-02')
source = source.replace('transfer-bound-ordinary-checkpoint', 'transfer-ordinary-index-delivery-checkpoint')
source = source.replace('bound-ordinary-endpoint', 'ordinary-index-delivery-endpoint')
replace("MODULE = 'TransferBoundOrdinarySource01'", "MODULE = 'TransferOrdinaryIndexDelivery01'")
replace('assert len(fresh) == 12', 'assert len(fresh) == 6')
replace("assert pool['objects'] == 12 and len(pool['inherited_public_reports']) == 162", "assert pool['objects'] == 16 and len(pool['inherited_public_reports']) == 221")
replace("manager_endpoint = DIAG / 'transfer-ordinary-storage-endpoint-20261011-01'", "manager_endpoint = DIAG / 'transfer-bound-ordinary-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-ordinary-storage-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-bound-ordinary-endpoint01.tar.xz'")
replace('428a659fe44b3dd53be178bba4b3f50d2893616646bf67905ffab997475c2e53', '316f55d8f00be6988ed16c0c1e74af460372d73cd5c35e60d25e671d69a7af7d')
replace("'module': 'TransferOrdinaryStorageSource01'", "'module': 'TransferBoundOrdinarySource01'")
source = source.replace('equality', 'inspection')
source = source.replace('transfer-verification-inspection-endpoint-20261011-01', 'transfer-index-inspection-endpoint-20261011-01')
source = source.replace('portable-windows-verification-inspection-endpoint01.tar.xz', 'portable-windows-index-inspection-endpoint01.tar.xz')
replace('13a3e1d2302d436a80e88221274b11b2c2469f652b25feefa381cdc4b3c19c77', '992c3cd13087d2212adde344d0302a709e835925d4d4c25fc9e71f88a78ae777')
replace("tar.extractfile('reports/fresh-13-complete-declarations.txt')", "tar.extractfile('reports/fresh-16-complete-declarations.txt')")
replace('assert len(inspection_reports) == 13', 'assert len(inspection_reports) == 16')
replace('assert len(combined_reports) == 162', 'assert len(combined_reports) == 221')
replace("'module': 'TransferVerificationEqualitySource01'", "'module': 'TransferIndexInspectionFacts01'")
replace('assert len(manager_selected) == 12', 'assert len(manager_selected) == 16')
replace("assert manager_reference['ancestors']['ancestors']['ancestors']['ancestors']['core_floor']['original'] == plan['external_floor']", """def core_floor_refs(value):
    if isinstance(value, dict):
        if 'core_floor' in value:
            yield value['core_floor']['original']
        for nested in value.values():
            yield from core_floor_refs(nested)
    elif isinstance(value, list):
        for nested in value:
            yield from core_floor_refs(nested)
assert plan['external_floor'] in list(core_floor_refs(manager_reference))""")
replace("reference = {'ordinary_storage':", "reference = {'bound_ordinary':")
replace("'status': 'PARENT_REVIEW_ACCEPTED_AND_PUBLISHED_22a1ab0491ad7e744aca9cfa8e1eca65b54c7e61', 'imported_complete_reports': 13", "'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE', 'imported_complete_reports': 16")
replace("'complete_owned_modules': 12, 'inherited_complete_reports': 162", "'complete_owned_modules': 16, 'inherited_complete_reports': 221")
replace('Exact twelve-module union of Ordinary storage and capability/Verification inspection; shared five-module raw sources/objects and 84 reports counted once. No ancestors replayed here.',
    'Exact sixteen-module union of bound Ordinary body and concrete index inspection; shared StateDelta/Raw sources/objects and 28 reports counted once. No ancestors replayed here.')
source = source.replace('two bound body/delivery definitions and ten finite source/inspection/cache/read/write/refusal proofs', 'one body/index API definition and five finite whole-call success/inspection/frame/marker proofs')
replace("add(stdout, 'reports/fresh-12-complete-declarations.txt'", "add(stdout, 'reports/fresh-6-complete-declarations.txt'")
source = source.replace('complete twelve-module first import root', 'complete sixteen-module first import root')
source = source.replace('verified 162 inherited reports', 'verified 221 inherited reports')
source = source.replace('transfer-bound-ordinary-source-20261011-01', 'transfer-ordinary-index-delivery-20261011-01')
source = source.replace('WHOLE_ITEM_REEXTRACTION_DERIVES_ORDINARY_MARKERS_AND_ENCLOSING_DELIVERY_REFUSAL_QUALIFIED', 'WHOLE_ORDINARY_PER_TRANSACTION_DELIVERY_DERIVES_BODY_MARKERS_AND_CONCRETE_INDEX_WRITES_QUALIFIED')
source = source.replace("'fresh_definition_audits': 2, 'fresh_theorem_audits': 10", "'fresh_definition_audits': 1, 'fresh_theorem_audits': 5")
source = source.replace("'fresh_complete_public_audits': 12", "'fresh_complete_public_audits': 6")
source = source.replace("'inherited_complete_public_audits': 162", "'inherited_complete_public_audits': 221")
start = source.index("    'scope': mapping['scope'] + ")
end = source.index("\ndump(ROOT / 'review.json', review)", start)
source = source[:start] + """    'scope': mapping['scope'] + ' One executable definition and all five theorem contracts are unchanged from failed01; two proof reductions now consume actual cache-selection observation and an already-rewritten height equality. Generic body success is derived from enclosing run success before instantiating the bound Ordinary source. Actual transaction/action projection, stateless extractor/token/proof provenance, Rust/tree/store/codecs/native and durability remain explicit interfaces. Failed predecessor full zero credit.'}
""".rstrip() + source[end:]
source = source.replace("'fresh_audits': 12", "'fresh_audits': 6").replace("'inherited_audits': 162", "'inherited_audits': 221")
(ROOT / 'assemble.py').write_text(source)
print({'fresh_reports': 6, 'inherited_reports': 221, 'owned_modules': 16})
