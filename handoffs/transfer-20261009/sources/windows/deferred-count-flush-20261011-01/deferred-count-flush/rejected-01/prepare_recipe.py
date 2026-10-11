"""Fresh complete deferred flush consumer; all ancestors and guards unchanged."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-deferred-count-walk-20261011-02/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-ordinary-decodable-index-20261011-01'", "UPSTREAM = DIAG / 'transfer-deferred-count-walk-20261011-02'")
s=s.replace('transfer-deferred-count-walk-owned-floor-20261011-02','transfer-deferred-count-flush-owned-floor-20261011-01')
s=s.replace("MODULE = 'TransferDeferredCountWalk01'", "MODULE = 'TransferDeferredCountFlush01'")
s=s.replace('TransferOrdinaryDecodableIndex01','TransferDeferredCountWalk01')
replace('assert len(current) == 1','assert len(current) == 4')
start=s.index("DEFERRED = DIAG / 'transfer-deferred-queue-model-20261010-03'")
end=s.index('assert len(records) == 27 and len(audits) == 301',start)
s=s[:start]+s[end:]
replace('assert len(records) == 27 and len(audits) == 301','assert len(records) == 28 and len(audits) == 305')
replace("'objects': 27", "'objects': 28")
s=s.replace('Complete twenty-seven-module first owned root; 301 inherited full reports.','Complete twenty-eight-module first owned root; 305 inherited full reports.')
replace('assert len(names) == 4','assert len(names) == 3')
replace("'imports': ['ShielddSecurity.TransferDeferredCountWalk01','ShielddSecurity.TransferDeferredQueueSourceModel01']", "'imports': ['ShielddSecurity.TransferDeferredCountWalk01']")
start=s.index("mapping = {'runtime_sha'"); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Whole successful nonempty deferred flush with concrete current-overlay writer and u64 codec derives decoded final count equal to initial count plus queue length, no wrap, drained queue and preserved original parent verifiable data/objects. New index child emits no events. Step and arbitrary-list V/object/event frames follow actual writeIndex operations without callback-frame premises. Original count observation and acquisition/height-success inputs are explicit; earlier genuine parent effects are preserved as parent state. Rust/ownership/byte/key/proof/native/Host/durability and full Transfer correspondence remain open. No new native or semantic negative-control credit.'}
""".rstrip()+s[end:]
s=s.replace('ARBITRARY_DEFERRED_WALK_DERIVES_COUNT_INCREASE_WITHOUT_U64_WRAP','WHOLE_DEFERRED_FLUSH_DERIVES_COUNT_QUEUE_AND_NON_INDEX_EFFECT_PRESERVATION')
s=s.replace('DEFERRED_COUNT_WALK_COMPLETE_TWENTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','DEFERRED_COUNT_FLUSH_COMPLETE_TWENTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 4, 'inherited_audits': 301", "'fresh_audits': 3, 'inherited_audits': 305")
s=s.replace('complete twenty-seven-module owned root','complete twenty-eight-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh finite step/arbitrary-walk framing and successful whole deferred-flush count/effect composition; all inherited proofs and guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':3,'inherited_audits':305,'owned_modules':28})
