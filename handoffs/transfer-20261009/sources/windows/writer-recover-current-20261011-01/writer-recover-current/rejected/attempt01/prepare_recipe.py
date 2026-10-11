"""Prepare actual current snapshot and captured recovery composition."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-host-seal-20261011-02/prepare.py').read_text()
def replace(a,b,count=1):
    global s
    assert s.count(a)==count,(a,s.count(a))
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-host-end-block-20261011-01'", "UPSTREAM = DIAG / 'transfer-host-seal-20261011-02'")
replace("POOL = DIAG / 'transfer-host-seal-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-writer-recover-current-owned-floor-20261011-01'")
replace("MODULE = 'TransferHostSeal01'", "MODULE = 'TransferWriterRecoverCurrent01'")
replace("stdout = UPSTREAM / 'runs/01-TransferHostEndBlock01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferHostSeal01/stdout.txt'")
replace("assert len(current) == 10", "assert len(current) == 7")
replace("records.append(('TransferHostEndBlock01'", "records.append(('TransferHostSeal01'")
replace("    'handwritten/TransferHostEndBlock01.lean', 'project/ShielddSecurity/TransferHostEndBlock01.lean']", "    'handwritten/TransferHostSeal01.lean', 'project/ShielddSecurity/TransferHostSeal01.lean']")
replace("assert len(records) == 66 and len(audits) == 663", "assert len(records) == 67 and len(audits) == 670")
replace("'objects': 66", "'objects': 67")
s=s.replace('sixty-six-module','sixty-seven-module').replace('663 inherited','670 inherited')
replace("assert len(names) == 7", "assert len(names) == 13")
start=s.index('\nmapping = '); end=s.index('\nmapping_file',start)
scope='Source recover_current chooses default boundary only at actual u64::MAX snapshot version; otherwise actual snapshot root and authenticated boundary reader select the current boundary. Actual lock outcome supplies exact Store input to captured-initial recovery. Clean recovery derives final root and 16-partition/history checks, Ready and stored boundary, with health equal only independently observed healthyAfter. No healthy/restoration conclusion is assumed, and this final-check theorem does not require legacy loop equivalence or forward partition frames. Failed recovery retains actual physical progress and Interrupted owner. Snapshot own-root authentication is distinct from external Host committed-root validation; immutable snapshot raw/proof coherence and ICS23 verifier soundness remain separate premises. Native temporal root/poison observations, captured initial selection/partition frames, finite version/root/serde/Clone/locks/owner/library/OS durability correspondence remain interfaces. Thirteen complete reports (eight data/program definitions, five proofs); zero native/control/full certification.'
s=s[:start]+"\nmapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ["+repr(scope)+"],\n    'scope': "+repr(scope)+"}"+s[end:]
replace("'imports': ['ShielddSecurity.TransferHostEndBlock01']", "'imports': ['ShielddSecurity.TransferHostSeal01']")
start=s.index("plan['kind'] = ");end=s.index("plan['artifact_policy']",start)
s=s[:start]+"plan['kind'] = 'SOURCE_WRITER_RECOVER_CURRENT_ACTUAL_SNAPSHOT_LOCK_AND_CAPTURED_PHYSICAL_RECOVERY'\nplan['scope'] = mapping['scope']\nplan['source_repairs'] = 'Fresh source composition; prior whole rejected attempts retained with zero credit. No guard changes.'\n"+s[end:]
replace("HOST_SEAL_COMPLETE_SIXTY_SIX_MODULE_CLOSURE_SELF_REVIEWED_UNRUN", "WRITER_CURRENT_RECOVERY_COMPLETE_SIXTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN")
replace("'fresh_audits': 7, 'inherited_audits': 663", "'fresh_audits': 13, 'inherited_audits': 670")
(ROOT/'prepare.py').write_text(s)
print({'fresh_definitions_and_proofs':13,'reused_modules':67,'reused_full_reports':670,'scope':scope})
