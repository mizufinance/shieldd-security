"""Prepare snapshot root/proof/reader/height composition with explicit value coherence."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-boundary-reader-source-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-boundary-key-binding-20261011-01'", "UPSTREAM = DIAG / 'transfer-boundary-reader-source-20261011-02'")
replace("POOL = DIAG / 'transfer-boundary-reader-source-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-authenticated-boundary-source-owned-floor-20261011-01'")
replace("MODULE = 'TransferBoundaryReaderSource01'", "MODULE = 'TransferAuthenticatedBoundarySource01'")
replace("stdout = UPSTREAM / 'runs/01-TransferBoundaryKeyBinding01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferBoundaryReaderSource01/stdout.txt'")
replace("records.append(('TransferBoundaryKeyBinding01'", "records.append(('TransferBoundaryReaderSource01'")
replace("'generate.py', 'generation.json', 'generated/TransferBoundaryKeyBinding01.lean', 'project/ShielddSecurity/TransferBoundaryKeyBinding01.lean'", "'repair_recipe.py', 'handwritten/TransferBoundaryReaderSource01.lean', 'project/ShielddSecurity/TransferBoundaryReaderSource01.lean'")
replace('assert len(current) == 11','assert len(current) == 7')
replace('assert len(records) == 54 and len(audits) == 544','assert len(records) == 55 and len(audits) == 551')
replace("'objects': 54", "'objects': 55")
s=s.replace('Complete fifty-four-module first owned root; 544 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete fifty-five-module first owned root; 551 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 7','assert len(names) == 9')
replace("'imports': ['ShielddSecurity.TransferBoundaryKeyBinding01']", "'imports': ['ShielddSecurity.TransferBoundaryReaderSource01']")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Source read_committed_boundary compares actual snapshot root to host commitment, then symbolically verifies actual get_with_proof values for exact ordered boundary/root/format source keys before actual boundary read and snapshot height comparison. Actual key authentication derives observed value/proof and verifier return; successful key-list recurrence derives each key check. Whole returned boundary success derives root equality, every key check, actual source reader success and observed snapshot height equality. Whole returned success binds actual raw key values to modeled root membership only under explicit immutable snapshot get_with_proof/get_raw consistency and independent membership verifier soundness contracts. Nine reports (five data/program definitions, four proofs), strict finite/physical audit guards unchanged. Native ICS23/ibc path/spec/root/byte/typed finite/key/serde/hash/immutable snapshot/owner/async/durability correspondence remains explicit. No native/control/full Transfer certification; proof success alone does not infer raw value coherence or consensus authentication.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Source proof observation contains actual nonmissing value bytes and proof; verify interface models native membership verification with application root, exact source key path and that value. Whole source success derives every callback return. Modeled Member semantics requires separately supplied verifier soundness; native ICS23/ibc spec/path/root/finite bytes correspondence is open. Binding raw read values requires immutable snapshot consistency between actual get_with_proof values and actual raw getter values, which is never inferred from a file hash or mere returned verifier success. Snapshot root and block height are actual independent fallible observations; host root authentication and owner/async/Clone/durability remain interfaces.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_BOUNDARY_READER_ACTUAL_BYTES_FORMAT_DECODE_HEIGHT_AND_ROOTS','SOURCE_AUTHENTICATED_BOUNDARY_ROOT_KEY_PROOFS_READER_HEIGHT_AND_VALUE_COHERENCE')
s=s.replace('BOUNDARY_READER_SOURCE_COMPLETE_FIFTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','AUTHENTICATED_BOUNDARY_SOURCE_COMPLETE_FIFTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 7, 'inherited_audits': 544", "'fresh_audits': 9, 'inherited_audits': 551")
s=s.replace('complete fifty-four-module owned root','complete fifty-five-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh source snapshot root/proof recurrence/actual reader/height composition; native verifier and immutable snapshot correspondence are explicit rather than axioms. Guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':9,'inherited_audits':551,'owned_modules':55})
