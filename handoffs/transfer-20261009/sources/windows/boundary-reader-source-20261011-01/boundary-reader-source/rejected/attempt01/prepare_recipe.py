"""Prepare actual boundary reader checks and noninitial source staging join."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-stage-boundary-source-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-store-commit-source-20261011-02'", "UPSTREAM = DIAG / 'transfer-boundary-key-binding-20261011-01'")
replace("POOL = DIAG / 'transfer-stage-boundary-source-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-boundary-reader-source-owned-floor-20261011-01'")
replace("MODULE = 'TransferStageBoundarySource01'", "MODULE = 'TransferBoundaryReaderSource01'")
replace("stdout = UPSTREAM / 'runs/01-TransferStoreCommitSource01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferBoundaryKeyBinding01/stdout.txt'")
replace("records.append(('TransferStoreCommitSource01'", "records.append(('TransferBoundaryKeyBinding01'")
replace("'repair_recipe.py', 'handwritten/TransferStoreCommitSource01.lean', 'project/ShielddSecurity/TransferStoreCommitSource01.lean'", "'generate.py', 'generation.json', 'generated/TransferBoundaryKeyBinding01.lean', 'project/ShielddSecurity/TransferBoundaryKeyBinding01.lean'")
replace('assert len(current) == 13','assert len(current) == 11')
replace('assert len(records) == 52 and len(audits) == 518','assert len(records) == 54 and len(audits) == 544')
replace("'objects': 52", "'objects': 54")
s=s.replace('Complete fifty-two-module first owned root; 518 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete fifty-four-module first owned root; 544 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 15','assert len(names) == 7')
replace("'imports': ['ShielddSecurity.TransferStoreCommitSource01']", "'imports': ['ShielddSecurity.TransferBoundaryKeyBinding01']")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Source read_boundary actual available/raw boundary bytes, pinned FORMAT availability/equality, fallible serde decode, present decoded height and available aggregate-root byte equality in native order. Whole returned boundary success derives every earlier primitive observation, actual bytes/decode and exact returned roots commitment check. Missing boundary refuses without default initialization; wrong format refuses before decoded boundary. Actual source reader installed into source stage_boundary derives previous application boundary bytes/decode/FORMAT/root observations on noninitial whole stage success. Seven reports (three data/program definitions, four proofs), finite/physical/strict audit guards unchanged. Native key projection/current immutable view/raw availability/typed u64/finite roots/blockId/serde/root SHA256 correspondence, Clone/owner/async/locking/durability remain primitive interfaces. read_boundary is not independent consensus authentication or ICS23 proof; authenticated snapshot selection remains separate. No native/control/full Transfer certification.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Actual source boundary reader checks original available current raw bytes and native literal FORMAT before decode/height/root check. Primitive serde/roots commitment/raw current getters and native immutable typed values/availability/ownership/async/locks remain explicit; hash identity does not establish correspondence. installReader synchronizes source stage availability, readPrevious, pinned FORMAT and aggregate-root callback with this reader; whole noninitial stage success derives original read observations. This reader consumes assumed authenticated application state and does not independently prove consensus or ICS23 snapshot authentication.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_STAGE_BOUNDARY_VALIDATION_PARENT_GATES_AND_EXACT_WRITES','SOURCE_BOUNDARY_READER_ACTUAL_BYTES_FORMAT_DECODE_HEIGHT_AND_ROOTS')
s=s.replace('STAGE_BOUNDARY_SOURCE_COMPLETE_FIFTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','BOUNDARY_READER_SOURCE_COMPLETE_FIFTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 15, 'inherited_audits': 518", "'fresh_audits': 7, 'inherited_audits': 544")
s=s.replace('complete fifty-two-module owned root','complete fifty-four-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source actual boundary reader checks and installed source staging join; no ancestor replay or new native/authentication credit. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_audits':544,'owned_modules':54})
