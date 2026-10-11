"""Prepare finite reachable pending codec/erasure bridge."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-prepared-accepted-source-20261011-02/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-block-seal-join-20261011-01'", "UPSTREAM = DIAG / 'transfer-prepared-accepted-source-20261011-02'")
replace("POOL = DIAG / 'transfer-prepared-accepted-source-owned-floor-20261011-02'", "POOL = DIAG / 'transfer-pending-finite-codec-owned-floor-20261011-02'")
replace("MODULE = 'TransferPreparedAcceptedSource01'", "MODULE = 'TransferPendingFiniteCodec01'")
replace("stdout = UPSTREAM / 'runs/01-TransferBlockSealJoin01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferPreparedAcceptedSource01/stdout.txt'")
replace("records.append(('TransferBlockSealJoin01'", "records.append(('TransferPreparedAcceptedSource01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferBlockSealJoin01.lean', 'project/ShielddSecurity/TransferBlockSealJoin01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferPreparedAcceptedSource01.lean', 'project/ShielddSecurity/TransferPreparedAcceptedSource01.lean']]")
replace('assert len(current) == 5','assert len(current) == 10')
replace('assert len(records) == 44 and len(audits) == 430','assert len(records) == 45 and len(audits) == 440')
replace("'objects': 44", "'objects': 45")
s=s.replace('Complete forty-four-module first owned root; 430 inherited full reports; shared StateDelta/Readback included exactly once.', 'Complete forty-five-module first owned root; 440 inherited full reports; shared StateDelta/Readback included exactly once.')
replace('assert len(names) == 10','assert len(names) == 12')
replace("'imports': ['ShielddSecurity.TransferBlockSealJoin01']", "'imports': ['ShielddSecurity.TransferPreparedAcceptedSource01']")
replace("plan['pins'].append(pin(ROOT / 'repair_recipe.py'))", "plan['pins'].append(pin(UPSTREAM / 'repair_recipe.py'))")
start=s.index('\nmapping = ')+1; end=s.index('\nmapping_file =',start)
scope='Finite enum erasure/ghost restoration models Open ordered vector plus finite membership set and Sealed ordered-only storage. Restored membership always has a finite list representation. Erasing an arbitrary model Pending canonicalizes membership; it restores the original model only under reachable coherence, with no roundtrip assumption for arbitrary infinite membership functions. Native Open append simulates model set membership union and Sealed drops the set while restoring exactly frozen membership. Typed finite codec assumption is observational after restoration, permitting native set deduplication/order changes. All twelve declaration conclusions/premises/axioms audited; finite list/enum symbolic reasoning. This module establishes the representation lemmas; existing generic whole-block theorems remain conditional until joined using coherence-restricted codec contracts. Native cnidarium typed embedding/Clone, imbl vector/set and actual nullifier value correspondence remain explicit interfaces. No native/control/storage/durability/full Transfer certification credit.'
s=s[:start]+"mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),\n    'interfaces': prior_mapping['interfaces'] + ['Finite NativePending Open member-list is an extensional representation of OrdSet membership; list order/duplicates may change in the concrete set codec. Sealed has ordered only and its model membership is reconstructed as a ghost. Typed finite object roundtrip is observational after restore, not identity of arbitrary model Pending functions. Whole block must consume a coherence-restricted roundtrip rather than instantiate the prior globally quantified abstract roundtrip with this native erasure codec. Native SDK nullifier finite value representation, cnidarium downcast/Clone and wrong-type panic interfaces remain explicit.'],\n    'scope': "+repr(scope)+"}"+s[end:]
s=s.replace('SOURCE_FROZEN_GLOBAL_INPUTS_DISCHARGE_STORE_PREPARE_CAPACITY_AND_DUPLICATE_GATES','FINITE_PENDING_ENUM_ERASURE_GHOST_AND_REACHABLE_COHERENT_CODEC')
s=s.replace('PREPARED_ACCEPTED_SOURCE_COMPLETE_FORTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','FINITE_PENDING_CODEC_COMPLETE_FORTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 10, 'inherited_audits': 430", "'fresh_audits': 12, 'inherited_audits': 440")
s=s.replace('complete forty-four-module owned root','complete forty-five-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh finite erasure/ghost simulation restricted to coherent reachable pending states; no universal arbitrary membership-function native roundtrip asserted. All physical/audit guards unchanged.'"+s[end:]
anchor = "plan['pins'] += mapping['runtime_sources']"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+"failed_codec = DIAG / 'transfer-pending-finite-codec-20261011-01'\nplan['pins'] += [pin(failed_codec / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferPendingFiniteCodec01.lean', 'project/ShielddSecurity/TransferPendingFiniteCodec01.lean', 'runs/01-TransferPendingFiniteCodec01/stdout.txt']]\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\n"+s[pos:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':12,'inherited_audits':440,'owned_modules':45})
