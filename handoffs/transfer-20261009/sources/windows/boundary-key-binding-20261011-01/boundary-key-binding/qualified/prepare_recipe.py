"""Prepare generated exact static boundary/legacy key and FORMAT binding."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-stage-boundary-source-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-store-commit-source-20261011-02'", "UPSTREAM = DIAG / 'transfer-stage-boundary-source-20261011-02'")
replace("POOL = DIAG / 'transfer-stage-boundary-source-owned-floor-20261011-01'", "POOL = DIAG / 'transfer-boundary-key-binding-owned-floor-20261011-01'")
replace("MODULE = 'TransferStageBoundarySource01'", "MODULE = 'TransferBoundaryKeyBinding01'")
replace("stdout = UPSTREAM / 'runs/01-TransferStoreCommitSource01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferStageBoundarySource01/stdout.txt'")
replace("records.append(('TransferStoreCommitSource01'", "records.append(('TransferStageBoundarySource01'")
replace("'repair_recipe.py', 'handwritten/TransferStoreCommitSource01.lean', 'project/ShielddSecurity/TransferStoreCommitSource01.lean'", "'repair_recipe.py', 'handwritten/TransferStageBoundarySource01.lean', 'project/ShielddSecurity/TransferStageBoundarySource01.lean'")
replace('assert len(current) == 13','assert len(current) == 15')
replace('assert len(records) == 52 and len(audits) == 518','assert len(records) == 53 and len(audits) == 533')
replace("'objects': 52", "'objects': 53")
s=s.replace('Complete fifty-two-module first owned root; 518 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete fifty-three-module first owned root; 533 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 15','assert len(names) == 11')
replace("handwritten = ROOT / 'handwritten' / (MODULE + '.lean')", "handwritten = ROOT / 'generated' / (MODULE + '.lean')")
replace("'imports': ['ShielddSecurity.TransferStoreCommitSource01']", "'imports': ['ShielddSecurity.TransferStageBoundarySource01']")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Generated exact ASCII source boundary/format/root/legacy-generation/legacy-set key bytes and native FORMAT literal from pinned Rust, with independent regeneration byte identity. Finite byte inequalities derive three write key inequalities under explicit injective representation. Source-bound actual stage success derives original transition validation/parent gates/fallible serialization, exact next serialized boundary bytes, pinned FORMAT bytes and observed roots commitment at the exact corresponding source keys, while nonverifiable/object state is framed. Eleven reports (eight data/program definitions, three proofs), strict finite/physical audit guards unchanged. Native key/current getter/availability/typed immutable values/serde/aggregate-root crypto/Clone/owner/concurrency/batch/durability remain interfaces; no hash-as-correspondence, native/control/full Transfer certification or extra assumption of desired writes.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Generated source keys and FORMAT use exact pinned ASCII literal extraction. Function.Injective project is the representation interface; source byte inequality discharges all three generic write-key separation premises. Native state/raw getter, typed values/serde, SHA256 roots commitment/owner/Clone/durability correspondence remains explicit and no output identity is elevated to a native certificate.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_STAGE_BOUNDARY_VALIDATION_PARENT_GATES_AND_EXACT_WRITES','SOURCE_BOUNDARY_LITERAL_KEYS_FORMAT_AND_EXACT_STAGE_WRITES')
s=s.replace('STAGE_BOUNDARY_SOURCE_COMPLETE_FIFTY_TWO_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','BOUNDARY_KEY_BINDING_COMPLETE_FIFTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 15, 'inherited_audits': 518", "'fresh_audits': 11, 'inherited_audits': 533")
s=s.replace('complete fifty-two-module owned root','complete fifty-three-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh maintained generator source byte binding with independent byte-identical regeneration; no generated hand edits or ancestor replay. Guards unchanged.'"+s[end:]
anchor="plan['pins'] += mapping['runtime_sources']"; assert s.count(anchor)==1
extra="""regenerated = DIAG / 'transfer-boundary-key-regeneration-20261011-01'
assert (regenerated / 'generated' / (MODULE + '.lean')).read_bytes() == handwritten.read_bytes()
plan['pins'] += [pin(ROOT / 'generate.py'), pin(ROOT / 'generation.json'), pin(regenerated / 'generation.json'), pin(regenerated / 'generated' / (MODULE + '.lean'))]
"""
s=s.replace(anchor,extra+anchor)
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':11,'inherited_audits':533,'owned_modules':53,'independent_regeneration':True})
