"""Join exact Ordinary and Verification objects; never replay ancestors."""
from pathlib import Path
import re
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
assert not (ROOT / 'prepare.py').exists()
source = (DIAG / 'transfer-ordinary-storage-source-20261011-02/prepare.py').read_text()
def replace(before, after):
    global source
    assert source.count(before) == 1, before
    source = source.replace(before, after)
replace("UPSTREAM = DIAG / 'transfer-current-volume-source-20261011-02'", "UPSTREAM = DIAG / 'transfer-ordinary-storage-source-20261011-02'")
source = source.replace('transfer-ordinary-storage-owned-floor-20261011-02', 'transfer-bound-ordinary-owned-floor-20261011-01')
source = source.replace("MODULE = 'TransferOrdinaryStorageSource01'", "MODULE = 'TransferBoundOrdinarySource01'")
source = source.replace('TransferCurrentVolumeSource01', 'TransferOrdinaryStorageSource01')
replace('assert len(current) == 9', 'assert len(current) == 12')
replace('assert len(records) == 9 and len(audits) == 126', 'assert len(records) == 10 and len(audits) == 138')
replace('POOL.mkdir()', '''equality = DIAG / 'transfer-verification-equality-source-20261011-02'
eq_plan = json.loads((equality / 'plan.json').read_bytes())
eq_pool = json.loads(Path(eq_plan['owned_import_pool']['path']).read_bytes())
eq_events = [json.loads(s) for s in (equality / 'events.jsonl').read_text().splitlines()]
assert len(eq_events) == 2 and eq_events[-1]['result']['status'] == 'passed'
eq_target = eq_plan['targets'][0]
eq_stdout = equality / 'runs/01-TransferVerificationEqualitySource01/stdout.txt'
eq_reports = m.audit(eq_stdout.read_text(), eq_target['audit_names'])
assert len(eq_reports) == 13 and eq_reports == eq_events[-1]['result']['audits']
assert pin(eq_stdout) == eq_events[-1]['result']['stdout']
for row in eq_pool['selected'] + [{'module': 'TransferVerificationEqualitySource01', 'source': eq_target['source'], 'object': eq_events[-1]['result']['objects'][0]}]:
    old = next((r for r in records if r[0] == row['module']), None)
    if old:
        assert old == (row['module'], row['source'], row['object'])
    else:
        records.append((row['module'], row['source'], row['object']))
for name, report in {**eq_pool['inherited_public_reports'], **eq_reports}.items():
    assert name not in audits or audits[name] == report
    audits[name] = report
inputs += eq_pool['input_records']
inputs += [pin(equality / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',
    'handwritten/TransferVerificationEqualitySource01.lean', 'project/ShielddSecurity/TransferVerificationEqualitySource01.lean']]
inputs.append(pin(eq_stdout))
assert len(records) == 12 and len(audits) == 162
POOL.mkdir()''')
replace("'objects': 9", "'objects': 12")
source = source.replace('Complete nine-module first owned root; 126 inherited full reports.', 'Complete twelve-module first owned root; 162 inherited full reports; shared five-module raw ancestry verified once.')
source = source.replace("ROOT / 'prepare_successor.py'", "ROOT / 'prepare_recipe.py'")
source = source.replace("'imports': ['ShielddSecurity.TransferOrdinaryStorageSource01']", "'imports': ['ShielddSecurity.TransferOrdinaryStorageSource01', 'ShielddSecurity.TransferVerificationEqualitySource01']")
start = source.index("mapping = {'runtime_sha':")
end = source.index("\nmapping_file = ROOT / 'source-mapping.json'", start)
source = source[:start] + """mapping = {'runtime_sha': '844389ee069e1fb2e576708842d0b389b4d9a44a',
    'runtime_sources': [pin(runtime / n) for n in ['crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
        'crates/crypto/proof-params/src/pari.rs', 'crates/core/component/shielded-pool/src/component/shielded_pool.rs',
        'third_party/cnidarium-0.83.0/src/delta.rs']],
    'interfaces': ['Ordinary token is explicit; actual stateless extractor, state/proof validation and registry gate provenance remain upstream',
        'Item statement denotes compared scalar value, envelope denotes serialized bytes; neither implies preimage semantic truth or cryptographic validity',
        'ensure_binds does not inspect registry_id; registry provenance is a separate enclosing gate',
        'Current overlay read availability/key/store correspondence and immutable successfully loaded SCT/tree/CloneCOW/codecs remain inherited',
        'Returned-result child discard is modeled; Rust panic, Host retry/publication and participating-store durability remain separate',
        'No native tests or semantic negative controls and no full Transfer certificate'],
    'scope': 'Whole Ordinary body performs stateless re-extraction and complete Item equality before both installed SCT/pending payload callbacks. Any returned result preserves input nonverifiable writes; family/scalar/envelope mismatch stops before every raw effect. Whole success derives exact re-extraction, initial current-overlay absence, both marker writes and visible marker values under explicit key separation. Existing current or parent entry prevents successful body/delivery and preserves original parent/queue without desired match, reshape, spent-read or rollback premises. Token/extractor/cryptographic/Rust/tree/store/native/durability interfaces and full Transfer remain open.'}
""".rstrip() + source[end:]
source = source.replace('BOTH_SCT_CALLBACKS_DERIVE_ORDINARY_STORAGE_FRAMING_AND_SUCCESS_MARKERS', 'EXACT_ITEM_REEXTRACTION_JOINS_ORDINARY_STORAGE_AND_DELIVERY_SOURCE')
start = source.index("plan['source_repairs'] = ")
end = source.index("\nplan['artifact_policy']", start)
source = source[:start] + "plan['source_repairs'] = 'Fresh finite source; exact common raw source/object/audit ancestry checked across both parent branches. No ancestor replay, guard relaxation or desired raw outcome premise.'" + source[end:]
source = source.replace('complete nine-module owned root', 'complete twelve-module owned root')
source = source.replace('ORDINARY_STORAGE_AND_COMPLETE_NINE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN', 'BOUND_ORDINARY_AND_COMPLETE_TWELVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
source = source.replace("'fresh_audits': 12, 'inherited_audits': 126", "'fresh_audits': 12, 'inherited_audits': 162")
(ROOT / 'prepare.py').write_text(source)
handwritten = ROOT / 'handwritten/TransferBoundOrdinarySource01.lean'
lean = handwritten.read_text()
names = re.findall(r'^(?:structure|inductive|def|theorem) ([A-Za-z0-9_]+)', lean, re.M)
assert len(names) == 12 and '#check' not in lean
audits = '\n'.join('set_option pp.all true in\n#check @' + n + '\n#print axioms ' + n for n in names)
lean = lean.replace('\nend ShielddSecurity.TransferBoundOrdinarySource01', '\n' + audits + '\n\nend ShielddSecurity.TransferBoundOrdinarySource01')
handwritten.write_text(lean)
print({'fresh_audits': len(names), 'inherited_audits': 162, 'owned_modules': 12})
