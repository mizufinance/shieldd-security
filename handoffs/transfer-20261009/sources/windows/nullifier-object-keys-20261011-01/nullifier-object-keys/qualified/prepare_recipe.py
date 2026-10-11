"""Prepare generated source-key retention join with exact regeneration pins."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'prepare.py').exists()
s=(DIAG/'transfer-pending-nullifier-retention-20261011-02/prepare.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
replace("UPSTREAM = DIAG / 'transfer-whole-nullifier-admission-20261011-01'", "UPSTREAM = DIAG / 'transfer-pending-nullifier-retention-20261011-02'")
s=s.replace('transfer-pending-nullifier-retention-owned-floor-20261011-02','transfer-nullifier-object-keys-owned-floor-20261011-01')
replace("MODULE = 'TransferPendingNullifierRetention01'", "MODULE = 'TransferNullifierObjectKeys01'")
replace("stdout = UPSTREAM / 'runs/01-TransferWholeNullifierAdmission01/stdout.txt'", "stdout = UPSTREAM / 'runs/01-TransferPendingNullifierRetention01/stdout.txt'")
replace("records.append(('TransferWholeNullifierAdmission01'", "records.append(('TransferPendingNullifierRetention01'")
replace("inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferWholeNullifierAdmission01.lean', 'project/ShielddSecurity/TransferWholeNullifierAdmission01.lean']]", "inputs += [pin(UPSTREAM / n) for n in ['plan.json', 'events.jsonl', 'execute_bounded.py', 'source-mapping.json',\n    'handwritten/TransferPendingNullifierRetention01.lean', 'project/ShielddSecurity/TransferPendingNullifierRetention01.lean']]")
replace("'imports': ['ShielddSecurity.TransferWholeNullifierAdmission01']", "'imports': ['ShielddSecurity.TransferPendingNullifierRetention01']")
replace('assert len(current) == 6','assert len(current) == 11')
replace('assert len(records) == 33 and len(audits) == 325','assert len(records) == 34 and len(audits) == 336')
replace("'objects': 33", "'objects': 34")
s=s.replace('Complete thirty-three-module first owned root; 325 inherited full reports.', 'Complete thirty-four-module first owned root; 336 inherited full reports.')
replace('assert len(names) == 11','assert len(names) == 7')
replace("handwritten = ROOT / 'handwritten' / (MODULE + '.lean')", "handwritten = ROOT / 'generated' / (MODULE + '.lean')")
start=s.index("mapping = {'runtime_sha'"); end=s.index("\nmapping_file =",start)
s=s[:start]+"""generation = json.loads((ROOT / 'generation.json').read_bytes())
regen = DIAG / 'transfer-nullifier-object-keys-regeneration-20261011-01'
regeneration = json.loads((regen / 'generation.json').read_bytes())
assert handwritten.read_bytes() == (regen / 'generated' / (MODULE + '.lean')).read_bytes()
assert generation['output'] == pin(handwritten)
for row in generation['runtime_sources']:
    assert pin(row['path']) == row
runtime_rows = {row['path']: row for row in prior_mapping['runtime_sources']}
for row in generation['runtime_sources']:
    assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
    runtime_rows[row['path']] = row
mapping = {'runtime_sha': prior_mapping['runtime_sha'], 'runtime_sources': list(runtime_rows.values()),
    'interfaces': [value for value in prior_mapping['interfaces'] if not value.startswith('Pending-nullifier object key differs')] +
      ['Byte-key to Nat projection is explicitly injective and denotes representation equality preservation, not hash/cryptographic injectivity; actual Rust String/object-store/codec/ownership correspondence remains separate'],
    'scope': 'Generated exact ASCII bytes from pinned Rust pending-nullifier, SCT cache, pending-note and pending-volume static key literals. Kernel byte separation and an explicit injective representation projection discharge all three abstract object-key inequality premises in qualified same-action retention. Whole success in both complete-Item contexts and every index mode derives actual staged pending encoding visible at the named source key, bounded/non-sealed full input append and reader/pending freshness. Source strings and the imported whole contract are hash-pinned; independent regeneration is byte exact. No desired callback/frame/poststate, admitted pending value or separate object-key inequality is supplied. Nonempty input/capacity parameters and actual reader/getter/codec/token/proof/byte projection/ownership/tree/native/Host/durability correspondence and full Transfer certification remain open. No new native or negative-control credit.'}
""".rstrip()+s[end:]
needle="plan['pins'] += mapping['runtime_sources']"
assert s.count(needle)==1
s=s.replace(needle,"""plan['pins'] += [pin(ROOT / n) for n in ['generate.py', 'generation.json']]
plan['pins'] += [pin(regen / 'generation.json'), pin(regen / 'generated' / (MODULE + '.lean'))]
plan['pins'] += [generation['generator'], generation['upstream_contract_source']] + generation['runtime_sources']
"""+needle)
s=s.replace('WHOLE_TRANSFER_DELIVERY_RETAINS_ADMITTED_PENDING_NULLIFIER_ENCODING','EXACT_SOURCE_OBJECT_KEYS_DISCHARGE_WHOLE_PENDING_RETENTION_INEQUALITIES')
s=s.replace('PENDING_NULLIFIER_RETENTION_COMPLETE_THIRTY_THREE_MODULE_CLOSURE_SELF_REVIEWED_UNRUN','NULLIFIER_OBJECT_KEYS_COMPLETE_THIRTY_FOUR_MODULE_CLOSURE_SELF_REVIEWED_UNRUN')
s=s.replace("'fresh_audits': 11, 'inherited_audits': 325", "'fresh_audits': 7, 'inherited_audits': 336")
s=s.replace('complete thirty-three-module owned root','complete thirty-four-module owned root')
start=s.index("plan['source_repairs'] = "); end=s.index("\nplan['artifact_policy']",start)
s=s[:start]+"plan['source_repairs'] = 'Fresh maintained generator derives exact runtime literal bytes and source-key whole retention contract; independent byte-exact regeneration. Qualified proofs and guards unchanged.'"+s[end:]
(ROOT/'prepare.py').write_text(s)
print({'fresh_audits':7,'inherited_audits':336,'owned_modules':34,'regeneration_exact':True})
