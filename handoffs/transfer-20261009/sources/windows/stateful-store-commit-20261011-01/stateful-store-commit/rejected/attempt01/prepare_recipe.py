"""Prepare state-threaded observed physical commit without replaying ancestors."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-record-read-bound-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-durable-write-source-20261011-01'", "UPSTREAM = DIAG / 'transfer-record-read-bound-20261011-01'")
replace("POOL = DIAG / 'transfer-record-read-bound-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-stateful-store-commit-owned-floor-20261011-01'")
replace("MODULE = 'TransferRecordReadBound01'", "MODULE = 'TransferStatefulStoreCommit01'")
replace("stdout = UPSTREAM / 'runs/01-TransferDurableWriteSource01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferRecordReadBound01/stdout.txt'")
replace("records.append(('TransferDurableWriteSource01'", "records.append(('TransferRecordReadBound01'")
replace("'handwritten/TransferDurableWriteSource01.lean', 'project/ShielddSecurity/TransferDurableWriteSource01.lean'", "'generated/TransferRecordReadBound01.lean', 'project/ShielddSecurity/TransferRecordReadBound01.lean'")
replace('assert len(records) == 59 and len(audits) == 584','assert len(records) == 60 and len(audits) == 592')
replace("'objects': 59", "'objects': 60")
s=s.replace('Complete fifty-nine-module first owned root; 584 inherited full reports;', 'Complete sixty-module first owned root; 592 inherited full reports;')
replace("handwritten = ROOT / 'generated' / (MODULE + '.lean')", "handwritten = ROOT / 'handwritten' / (MODULE + '.lean')")
replace('assert len(names) == 8','assert len(names) == 13')
replace("'imports': ['ShielddSecurity.TransferDurableWriteSource01']", "'imports': ['ShielddSecurity.TransferRecordReadBound01']")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Actual-source Store commit gate/intent read/serialization equality precede readiness interruption, symbolic sessions threading observed physical roots and current poison-health ghosts, followed only after all session success by an independent final actual root/health observation and next-root check. Native read/callback observations are independent; no unchanged or healthy assumption. Thirteen reports (eight data/program definitions, five proofs) derive actual ordered state-threaded calls, failure physical progress/poison retention, owned ready/boundary frames, returned-success final roots and read blocking. Native ghost-snapshot refinement, NOMT partition/index/session ownership, current temporal root reads, serde/read_record, concurrent lock frames, finite typed embedding and OS durability remain correspondence interfaces. Zero native/control/full Transfer certification; ancestor snapshot-health results remain qualified by their original limits.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['New stateful commit threads physical root and poison-health observations across actual session results and final actual roots read while framing owned ready/boundary fields. Observations are ghosts, not added native calls. Model does not assume post-session health equals pre-session health and does not infer health from session success. State-threaded callbacks are independently observed outcomes; native ghost observation/current store/ownership/concurrent NOMT/lock/serialization correspondence still requires justification. Failure observes progress without rollback. Source-identical old snapshot-health model remains explicitly scoped, not upgraded by this theorem.'],\n    'scope': "+repr(scope)+"}"+s[end:]
start=s.index("regenerated = DIAG / 'transfer-record-read-regeneration-20261011-01'");end=s.index("plan['pins'] += mapping['runtime_sources']",start)
s=s[:start]+s[end:]
s=s.replace('SOURCE_RECORD_READ_TAKE_LIMIT_RETURNED_BYTE_BOUND_AND_REFUSALS','SOURCE_STATEFUL_STORE_COMMIT_OBSERVED_ROOTS_CURRENT_POISON_AND_OWNED_FRAMES')
s=s.replace('RECORD_READ_BOUND_COMPLETE_FIFTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','STATEFUL_STORE_COMMIT_COMPLETE_SIXTY_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 8, 'inherited_audits': 584", "'fresh_audits': 13, 'inherited_audits': 592")
s=s.replace('complete fifty-nine-module owned root','complete sixty-module owned root')
start=s.index("plan['source_repairs'] = ");end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh handwritten temporal state threading with independent actual physical/health observations; no ancestor replay, native control or physical durability credit. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':13,'inherited_audits':592,'owned_modules':60})
