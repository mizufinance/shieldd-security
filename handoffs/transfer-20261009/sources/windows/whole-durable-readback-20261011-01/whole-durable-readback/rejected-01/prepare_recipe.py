"""Prepare current durable Reader/full-body join with exact old Readback reports."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-current-pending-replay-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-nullifier-object-keys-20261011-01'", "UPSTREAM = DIAG / 'transfer-current-pending-replay-20261011-01'")
s=s.replace('transfer-current-pending-replay-owned-floor-20261011-01','transfer-whole-durable-readback-owned-floor-20261011-01')
replace("MODULE = 'TransferCurrentPendingReplay01'", "MODULE = 'TransferWholeDurableReadback01'")
replace("stdout = UPSTREAM / 'runs/01-TransferNullifierObjectKeys01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferCurrentPendingReplay01/stdout.txt'")
replace("records.append(('TransferNullifierObjectKeys01'", "records.append(('TransferCurrentPendingReplay01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'generated/TransferNullifierObjectKeys01.lean', 'project/ShielddSecurity/TransferNullifierObjectKeys01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferCurrentPendingReplay01.lean', 'project/ShielddSecurity/TransferCurrentPendingReplay01.lean']]")
replace('assert len(current) == 7','assert len(current) == 8')
replace('assert len(records) == 35 and len(audits) == 343',"""assert len(records) == 36 and len(audits) == 351
readback = DIAG / 'transfer-readback-recovery-publication-20261010-02'
readback_plan = json.loads((readback / 'plan.json').read_bytes())
readback_events = [json.loads(line) for line in (readback / 'events.jsonl').read_text().splitlines()]
readback_target = readback_plan['targets'][0]
assert readback_target['module'] == 'TransferReadback'
readback_result = readback_events[1]['result']
assert readback_result['status'] == 'passed'
readback_stdout = readback / 'runs/01-TransferReadback/stdout.txt'
readback_audits = m.audit(readback_stdout.read_text(), readback_target['audit_names'])
assert len(readback_audits) == 17 and readback_audits == readback_result['audits']
assert pin(readback_stdout) == readback_result['stdout']
assert set(audits).isdisjoint(readback_audits)
audits.update(readback_audits)
records.append(('TransferReadback', readback_target['source'], readback_result['objects'][0]))
inputs += [pin(readback / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'project/ShielddSecurity/TransferReadback.lean', 'runs/01-TransferReadback/stdout.txt']]
readback_endpoint = DIAG / 'transfer-readback-publication-endpoint-20261010-01'
inputs += [pin(readback_endpoint / n) for n in ['portable-windows-readback-publication-endpoint01.tar.xz', 'manifest.json', 'review.json']]
assert len(records) == 37 and len(audits) == 368""")
replace("'objects': 35", "'objects': 37")
s=s.replace('Complete thirty-five-module first owned root; 343 inherited full reports.', 'Complete thirty-seven-module first owned root; 368 inherited full reports including exactly seventeen original Readback reports.')
replace('assert len(names) == 8','assert len(names) == 11')
replace("'imports': ['ShielddSecurity.TransferNullifierObjectKeys01']", "'imports': ['ShielddSecurity.TransferCurrentPendingReplay01', 'ShielddSecurity.TransferReadback']")
start=s.index("runtime_rows = "); end=s.index("\nmapping_file =",start)
s=s[:start]+"""runtime_rows = {row['path']: row for row in prior_mapping['runtime_sources']}
for relative in ['crates/core/component/sct/src/permanent_nullifiers.rs', 'crates/core/component/sct/src/permanent_nullifiers/store.rs']:
    row = pin(runtime / relative)
    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
    runtime_rows[row['path']] = row
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),
    'interfaces': prior_mapping['interfaces'] + ['Current typed Reader object decode/Clone, application read_boundary authentication/codec, read-lock availability, candidate native proof construction, NOMT/SHA semantic correspondence and ownership/durability remain explicit. MerkleContract is an explicit semantic soundness premise, not proved by hashes. Wrong-type reader object panic is outside the returned-result model.'],
    'scope': 'Install current object-overlay typed Reader, observed application boundary, read-lock availability and verified status as the nullifier reader in both complete-Item whole delivery contexts/every index mode. Whole success with nonempty inputs/capacity below word limit derives verified unspent status for every actual input, store readiness/health/exact authenticated boundary/roots, bounded partition and exact verifier acceptance. Under the existing explicit Merkle soundness contract it derives semantic absence at each exact key/root. No store/reader/boundary/lock/proof/lookup success or desired pending poststate is supplied to whole-success theorems. Missing reader, boundary, lock and stale boundary derive unavailable and never unspent. Boundary/native/proof/typed/codec/crypto/Host/durability correspondence and full Transfer certification remain open; zero new native or semantic control credit.'}
""".rstrip()+s[end:]
s=s.replace('CURRENT_PENDING_OBJECT_READ_DERIVES_TWO_ACTION_SHARED_INPUT_REPLAY_REFUSAL','WHOLE_TRANSFER_SUCCESS_DERIVES_VERIFIED_DURABLE_READBACK_AND_CONDITIONAL_MERKLE_ABSENCE')
s=s.replace('CURRENT_PENDING_REPLAY_COMPLETE_THIRTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','WHOLE_DURABLE_READBACK_COMPLETE_THIRTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 8, 'inherited_audits': 343", "'fresh_audits': 11, 'inherited_audits': 368")
s=s.replace('complete thirty-five-module owned root','complete thirty-seven-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh current Reader/boundary/lock/verified status installation and whole-delivery semantic absence composition; exact old Readback source/object/17 full reports reused without replay; guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':11,'inherited_audits':368,'owned_modules':37})
