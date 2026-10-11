"""Seal exact max-count deferred refusal and retry with complete ancestry."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-deferred-count-flush-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
s=s.replace('transfer-deferred-count-flush-20261011-01','transfer-deferred-max-count-20261011-01')
s=s.replace('transfer-deferred-count-flush-checkpoint','transfer-deferred-max-count-checkpoint')
s=s.replace('deferred-count-flush-endpoint','deferred-max-count-endpoint')
replace("MODULE = 'TransferDeferredCountFlush01'", "MODULE = 'TransferDeferredMaxCount01'")
replace("assert pool['objects'] == 28 and len(pool['inherited_public_reports']) == 305", "assert pool['objects'] == 29 and len(pool['inherited_public_reports']) == 308")
replace("manager_endpoint = DIAG / 'transfer-deferred-count-walk-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-deferred-count-flush-endpoint-20261011-02'")
replace("manager_archive = manager_endpoint / 'portable-windows-deferred-count-walk-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-deferred-count-flush-endpoint01.tar.xz'")
replace('877959ca4c6697bb37dce8ed207e4a26537784731f9265bb0a7bd324345f9b87','3ebee7fe7c088e3e566ec68b8e52e33f5963b1c735f9ea0903dd4235f2821ec7')
replace("tar.extractfile('reports/fresh-4-complete-declarations.txt')", "tar.extractfile('reports/fresh-3-complete-declarations.txt')")
replace('assert len(manager_reports) == 4','assert len(manager_reports) == 3')
replace("'module': 'TransferDeferredCountWalk01'", "'module': 'TransferDeferredCountFlush01'")
replace('assert len(combined_reports) == 305','assert len(combined_reports) == 308')
replace('assert len(manager_selected) == 28','assert len(manager_selected) == 29')
replace("reference = {'deferred_count_walk':", "reference = {'deferred_count_flush':")
replace("'imported_complete_reports': 4},", "'imported_complete_reports': 3},")
replace("'complete_owned_modules': 28, 'inherited_complete_reports': 305", "'complete_owned_modules': 29, 'inherited_complete_reports': 308")
replace('Exact twenty-eight-module closure through the merged current-overlay/concrete-codec/deferred-walk branches, with all 305 inherited complete reports.', 'Exact twenty-nine-module closure through concrete u64 current reads and whole deferred-flush count/effect composition, with all 308 inherited complete reports.')
s=s.replace('three finite step/walk frame and successful whole-flush count/effect proofs','three exact max-count deferred walk/whole failure/empty retry proofs')
s=s.replace('complete twenty-eight-module first import root','complete twenty-nine-module first import root')
s=s.replace('verified 305 inherited reports','verified 308 inherited reports')
s=s.replace('WHOLE_DEFERRED_FLUSH_DERIVES_COUNT_QUEUE_AND_NON_INDEX_EFFECT_PRESERVATION_QUALIFIED','EXACT_MAX_COUNT_DERIVES_DEFERRED_FAILURE_QUEUE_DRAIN_AND_EMPTY_RETRY_QUALIFIED')
replace("'inherited_complete_public_audits': 305", "'inherited_complete_public_audits': 308")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"""    'scope': mapping['scope'] + ' All three handwritten theorems have complete original type/axiom reports. The error is existential because earlier failures are deliberately retained; only the separately qualified available-read theorem identifies intended semantic overflow. Queue consumption and failed same-instance reconstruction follow actual source-order flush, without a failed callback or final cache premise. Native genuine controls remain separate and unrun.'}
""".rstrip()+s[end:]
s=s.replace("'inherited_audits': 305", "'inherited_audits': 308")
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':3,'inherited_reports':308,'owned_modules':29})
