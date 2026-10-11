"""Seal the complete body-delivery/deferred-failure join with exact ancestry."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-deferred-max-count-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
s=s.replace('transfer-deferred-max-count-20261011-01','transfer-deferred-body-failure-20261011-01')
s=s.replace('transfer-deferred-max-count-checkpoint','transfer-deferred-body-failure-checkpoint')
s=s.replace('deferred-max-count-endpoint','deferred-body-failure-endpoint')
replace("MODULE = 'TransferDeferredMaxCount01'", "MODULE = 'TransferDeferredBodyFailure01'")
replace('assert len(fresh) == 3','assert len(fresh) == 4')
replace("assert pool['objects'] == 29 and len(pool['inherited_public_reports']) == 308", "assert pool['objects'] == 31 and len(pool['inherited_public_reports']) == 315")
replace("manager_endpoint = DIAG / 'transfer-deferred-count-flush-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-fee-funding-delivery-endpoint-20261011-03'")
replace("manager_archive = manager_endpoint / 'portable-windows-deferred-count-flush-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-fee-funding-delivery-endpoint01.tar.xz'")
replace('3ebee7fe7c088e3e566ec68b8e52e33f5963b1c735f9ea0903dd4235f2821ec7','6eccb37189e665ee644d757c3f451422ace5a4414ef7ed699ade427b4fbf9214')
s=s.replace('reports/fresh-3-complete-declarations.txt','reports/fresh-4-complete-declarations.txt')
replace('assert len(manager_reports) == 3','assert len(manager_reports) == 4')
replace("'module': 'TransferDeferredCountFlush01'", "'module': 'TransferFeeFundingDelivery01'")
replace('assert len(combined_reports) == 308','assert len(combined_reports) == 315')
replace('assert len(manager_selected) == 29','assert len(manager_selected) == 31')
replace("reference = {'deferred_count_flush':", "reference = {'fee_funding_delivery':")
replace("'imported_complete_reports': 3", "'imported_complete_reports': 4")
replace("'complete_owned_modules': 29, 'inherited_complete_reports': 308", "'complete_owned_modules': 31, 'inherited_complete_reports': 315")
replace('Exact twenty-nine-module closure through concrete u64 current reads and whole deferred-flush count/effect composition, with all 308 inherited complete reports.', 'Exact thirty-one-module closure through complete Ordinary/FeeFunding bodies and concrete deferred count/flush/failure source joins, with all 315 inherited complete reports.')
s=s.replace('three exact max-count deferred walk/whole failure/empty retry proofs','both-context body source definition and three deferred delivery/failed index/empty retry proofs')
s=s.replace('complete twenty-nine-module first import root','complete thirty-one-module first import root')
s=s.replace('verified 308 inherited reports','verified 315 inherited reports')
s=s.replace('EXACT_MAX_COUNT_DERIVES_DEFERRED_FAILURE_QUEUE_DRAIN_AND_EMPTY_RETRY_QUALIFIED','DEFERRED_BODY_DELIVERY_THEN_MAX_COUNT_FAILURE_DERIVES_EFFECT_PRESERVATION_QUEUE_AND_RETRY_QUALIFIED')
replace("'fresh_definition_audits': 0", "'fresh_definition_audits': 1")
replace("'fresh_complete_public_audits': 3", "'fresh_complete_public_audits': 4")
replace("'inherited_complete_public_audits': 308", "'inherited_complete_public_audits': 315")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"""    'scope': mapping['scope'] + ' The definition and all three handwritten theorems have complete original type/axiom reports. The delivered parent contains modeled body effects before indexing; failed flush preserves that parent and consumes the derived queue. This is not rollback to the pre-delivery parent. Error is existential and native genuine controls remain separate and unrun.'}
""".rstrip()+s[end:]
s=s.replace("'fresh_audits': 3, 'inherited_audits': 308", "'fresh_audits': 4, 'inherited_audits': 315")
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':315,'owned_modules':31})
