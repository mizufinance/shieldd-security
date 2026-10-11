"""Merge exactly the qualified deferred walk into the complete codec closure."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'plan.json').exists()
s=(DIAG/'transfer-ordinary-decodable-index-20261011-01/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-ordinary-max-count-20261011-02'", "UPSTREAM = DIAG / 'transfer-ordinary-decodable-index-20261011-01'")
s=s.replace('transfer-ordinary-decodable-index-owned-floor-20261011-01','transfer-deferred-count-walk-owned-floor-20261011-01')
s=s.replace("MODULE = 'TransferOrdinaryDecodableIndex01'", "MODULE = 'TransferDeferredCountWalk01'")
s=s.replace('TransferOrdinaryMaxCount01','TransferOrdinaryDecodableIndex01')
replace('assert len(current) == 6','assert len(current) == 1')
replace("'generated/TransferOrdinaryDecodableIndex01.lean'", "'handwritten/TransferOrdinaryDecodableIndex01.lean'")
replace('assert len(records) == 25 and len(audits) == 283', '''assert len(records) == 27 and len(audits) == 301''')
# Add one independently completed module, with exact shared state/floor identity.
before='POOL.mkdir()'
assert s.count(before)==1
extra='''DEFERRED = DIAG / 'transfer-deferred-queue-model-20261010-03'
dp = json.loads((DEFERRED / 'plan.json').read_bytes())
de = [json.loads(x) for x in (DEFERRED / 'events.jsonl').read_text().splitlines()]
assert len(de) == 2 and de[-1]['result']['status'] == 'passed'
dt = dp['targets'][0]
ds = DEFERRED / 'runs/01-TransferDeferredQueueSourceModel01/stdout.txt'
da = m.audit(ds.read_text(), dt['audit_names'])
assert len(da) == 17 and da == de[-1]['result']['audits'] and set(da).isdisjoint(audits)
assert pin(ds) == de[-1]['result']['stdout']
assert dp['external_floor'] == plan['external_floor']
for shared in dp['owned_imports']:
    assert any(shared['sha256'] == obj['sha256'] and shared['bytes'] == obj['bytes'] for _, _, obj in records)
records.append(('TransferDeferredQueueSourceModel01',dt['source'],de[-1]['result']['objects'][0]))
audits.update(da)
inputs += [pin(DEFERRED / n) for n in ['plan.json','events.jsonl','execute_bounded.py','source-mapping.json','project/ShielddSecurity/TransferDeferredQueueSourceModel01.lean']]
inputs.append(pin(ds))
'''
marker='assert len(records) == 27 and len(audits) == 301'
s=s.replace(marker,extra+'\n'+marker)
replace("'objects': 25", "'objects': 27")
s=s.replace('Complete twenty-five-module first owned root; 283 inherited full reports.','Complete twenty-seven-module first owned root; 301 inherited full reports.')
replace('assert len(names) == 1','assert len(names) == 4')
replace("'imports': ['ShielddSecurity.TransferOrdinaryDecodableIndex01']", "'imports': ['ShielddSecurity.TransferOrdinaryDecodableIndex01','ShielddSecurity.TransferDeferredQueueSourceModel01']")
start=s.index("mapping = {'runtime_sha'"); end=s.index("\nmapping_file =",start)
s=s[:start]+"""mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': prior_mapping['runtime_sources'],
    'interfaces': prior_mapping['interfaces'],
    'scope': 'Arbitrary-list deferred count recurrence with actual modeled current NV reads and concrete u64 codec: a successful index step derives the decoded next ordinal and increment; successful complete walk derives initial count plus queue length and excludes u64 wrap. Caller supplies only original input-state count observation and whole walk success, not per-step success/increment/desired cache or final counter. Reads remain availability-sensitive; genuine Rust/ownership/key/crypto/native/Host/durability and full Transfer correspondence remain open. No native or semantic negative-control credit.'}
""".rstrip()+s[end:]
s=s.replace('WHOLE_ORDINARY_SUCCESS_DERIVES_DECODABLE_CONCRETE_U64_INDEX_VALUES','ARBITRARY_DEFERRED_WALK_DERIVES_COUNT_INCREASE_WITHOUT_U64_WRAP')
s=s.replace('ORDINARY_DECODABLE_INDEX_COMPLETE_TWENTY_FIVE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','DEFERRED_COUNT_WALK_COMPLETE_TWENTY_SEVEN_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 1, 'inherited_audits': 283", "'fresh_audits': 4, 'inherited_audits': 301")
s=s.replace('complete twenty-five-module owned root','complete twenty-seven-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh symbolic arbitrary-list deferred count recurrence on exact merged qualified closures; all inherited proofs and guards unchanged.'"+s[end:]
s=s.replace('runner, handwritten, target_source, composition_file, mapping_file]', "runner, handwritten, target_source, composition_file, mapping_file, ROOT / 'prepare-rejected-owned-count.py', ROOT / 'prepare_recipe-rejected-owned-count.py']")
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':4,'inherited_audits':301,'owned_modules':27,'rejected_preparation_credit':0})
