"""Join the whole-delivery input recurrence to actual Host publication."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-end-to-end-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-writer-recover-current-20261011-02'", "UPSTREAM = DIAG / 'transfer-end-to-end-20261011-02'")
replace("POOL = DIAG / 'transfer-end-to-end-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-global-commit-join-owned-floor-20261011-01'")
replace("MODULE = 'TransferEndToEnd01'", "MODULE = 'TransferGlobalCommitJoin01'")
replace("stdout = UPSTREAM / 'runs/01-TransferWriterRecoverCurrent01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferEndToEnd01/stdout.txt'")
replace("records.append(('TransferWriterRecoverCurrent01'", "records.append(('TransferEndToEnd01'")
replace("    'handwritten/TransferWriterRecoverCurrent01.lean', 'project/ShielddSecurity/TransferWriterRecoverCurrent01.lean']", "    'handwritten/TransferEndToEnd01.lean', 'project/ShielddSecurity/TransferEndToEnd01.lean']")
replace("assert len(records) == 68 and len(audits) == 683", "assert len(records) == 69 and len(audits) == 696")
replace("'objects': 68", "'objects': 69")
s=s.replace('sixty-eight-module','sixty-nine-module').replace('683 inherited','696 inherited')
replace('assert len(names) == 13','assert len(names) == 5')
start=s.index('\nmapping = ');end=s.index('\nmapping_file',start)
scope='Whole successful delivery walk from actual encoded default Pending derives global exact ordered inputs, Nodup and source consensus capacity under finite NativePending codec observational roundtrip and projected key injectivity. Successful concrete deferred flush preserves original pending objects and V bytes for all modes/queues without supplied count observation; successful takeState transfers those exact fields. Explicit universal FinalizationPendingFrame constrains only actual returned application pending object to source SCT seal of its actual input, not desired accepted vector, successful participant callbacks or committed roots. Composed actual Host publication then derives same global accepted input vector, present application root, Idle/Ready and final observed recovery roots/stored boundary/16 partitions/current independently observed health. Five complete reports (two definitions including full finalization field contract; three proofs). Native component successful returned-field semantics/panics, finite typed codec/key/Clone/Any/Arc/lock ownership, snapshot raw/proof coherence plus separate ICS23 soundness, physical temporal/partition frames/hash/serde/library/OS durability and genuine runtime replay remain interfaces. Zero native/control/full certification.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"],\n    'scope': "+repr(scope)+"}"+s[end:]
replace("'imports': ['ShielddSecurity.TransferWriterRecoverCurrent01']", "'imports': ['ShielddSecurity.TransferEndToEnd01']")
start=s.index("plan['kind'] = ");end=s.index("plan['artifact_policy']",start)
s=s[:start]+"plan['kind'] = 'SOURCE_WHOLE_GLOBAL_INPUTS_TO_HOST_PUBLICATION_UNDER_FINITE_CODEC_AND_FINALIZATION_FIELD_CONTRACT'\nplan['scope'] = mapping['scope']\nplan['source_repairs'] = 'Fresh source join; prior whole rejected attempts retained with zero credit. No guard changes.'\n"+s[end:]
replace('COMPOSED_TRANSFER_PIPELINE_COMPLETE_SIXTY_EIGHT_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','GLOBAL_COMMIT_JOIN_COMPLETE_SIXTY_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
replace("'fresh_audits': 13, 'inherited_audits': 683", "'fresh_audits': 5, 'inherited_audits': 696")
(ROOT/'prepare.py').write_text(s)
print({'fresh_definitions_and_proofs':5,'reused_modules':69,'reused_full_reports':696,'scope':scope})
