"""Prepare current typed pending read and two-action shared-input refusal."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-pending-nullifier-retention-20261011-02/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-whole-nullifier-admission-20261011-01'", "UPSTREAM = DIAG / 'transfer-nullifier-object-keys-20261011-01'")
s=s.replace('transfer-pending-nullifier-retention-owned-floor-20261011-02','transfer-current-pending-replay-owned-floor-20261011-01')
replace("MODULE = 'TransferPendingNullifierRetention01'", "MODULE = 'TransferCurrentPendingReplay01'")
replace("stdout = UPSTREAM / 'runs/01-TransferWholeNullifierAdmission01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferNullifierObjectKeys01/stdout.txt'")
replace("records.append(('TransferWholeNullifierAdmission01'", "records.append(('TransferNullifierObjectKeys01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferWholeNullifierAdmission01.lean', 'project/ShielddSecurity/TransferWholeNullifierAdmission01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'generated/TransferNullifierObjectKeys01.lean', 'project/ShielddSecurity/TransferNullifierObjectKeys01.lean']]")
replace("'imports': ['ShielddSecurity.TransferWholeNullifierAdmission01']", "'imports': ['ShielddSecurity.TransferNullifierObjectKeys01']")
replace('assert len(current) == 6','assert len(current) == 7')
replace('assert len(records) == 33 and len(audits) == 325','assert len(records) == 35 and len(audits) == 343')
replace("'objects': 33", "'objects': 35")
s=s.replace('Complete thirty-three-module first owned root; 325 inherited full reports.', 'Complete thirty-five-module first owned root; 343 inherited full reports.')
replace('assert len(names) == 11','assert len(names) == 8')
start=s.index("mapping = {'runtime_sha'"); end=s.index("\nmapping_file =",start)
s=s[:start]+"""runtime_rows = {row['path']: row for row in prior_mapping['runtime_sources']}
for relative in ['third_party/cnidarium-0.83.0/src/read.rs', 'crates/core/component/sct/src/component/tree.rs']:
    row = pin(runtime / relative)
    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
    runtime_rows[row['path']] = row
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),
    'interfaces': prior_mapping['interfaces'] + ['The object decoder denotes successful typed object_get/Clone, with forall-pending encode/decode roundtrip explicit. Present wrong-type object_get/object_put panics are outside returned-result correspondence and are not modeled as default or recoverable refusal.'],
    'scope': 'Install pending getter from the current object overlay: actual absence returns Open empty; retained encoded pending derives the corresponding typed decoded value under an explicit object representation roundtrip. Whole first delivery in either proof context/every index mode derives retained named-key pending membership for a shared input. This state observation excludes second whole delivery success for arbitrary second proof context/mode/registry/exclusivity, volume keys/payload and all reader/extractor/callback outcomes, preserving the first delivered parent/deferred queue through enclosing finish. No caller-supplied first pending poststate, already-spent predicate, lookup/height failure, successful primitive or desired second error is supplied to the two-action theorem. Shared membership in both action input projections and capacity below word limit are explicit. Wrong-type/loader panics and actual Rust typed getter/Clone/object codec/store/proof/key/tree/native/Host/durability correspondence and full Transfer certification remain open. No new native or semantic control execution credit.'}
""".rstrip()+s[end:]
s=s.replace('WHOLE_TRANSFER_DELIVERY_RETAINS_ADMITTED_PENDING_NULLIFIER_ENCODING','CURRENT_PENDING_OBJECT_READ_DERIVES_TWO_ACTION_SHARED_INPUT_REPLAY_REFUSAL')
s=s.replace('PENDING_NULLIFIER_RETENTION_COMPLETE_THIRTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','CURRENT_PENDING_REPLAY_COMPLETE_THIRTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 11, 'inherited_audits': 325", "'fresh_audits': 8, 'inherited_audits': 343")
s=s.replace('complete thirty-three-module owned root','complete thirty-five-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh finite current-overlay typed pending read and whole two-action shared-input replay composition; qualified ancestors and physical/audit guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':8,'inherited_audits':343,'owned_modules':35})
