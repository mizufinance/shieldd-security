"""Seal original all-input admission reports and exact runtime source associations."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-deferred-max-count-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
s=s.replace('transfer-deferred-max-count-20261011-01','transfer-whole-nullifier-admission-20261011-01')
s=s.replace('transfer-deferred-max-count-checkpoint','transfer-whole-nullifier-admission-checkpoint')
s=s.replace('deferred-max-count-endpoint','whole-nullifier-admission-endpoint')
replace("MODULE = 'TransferDeferredMaxCount01'", "MODULE = 'TransferWholeNullifierAdmission01'")
replace('assert len(fresh) == 3','assert len(fresh) == 6')
replace("assert pool['objects'] == 29 and len(pool['inherited_public_reports']) == 308", "assert pool['objects'] == 32 and len(pool['inherited_public_reports']) == 319")
replace("manager_endpoint = DIAG / 'transfer-deferred-count-flush-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-deferred-body-failure-endpoint-20261011-03'")
replace("manager_archive = manager_endpoint / 'portable-windows-deferred-count-flush-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-deferred-body-failure-endpoint01.tar.xz'")
replace('3ebee7fe7c088e3e566ec68b8e52e33f5963b1c735f9ea0903dd4235f2821ec7','1c2258413fcceaeb39e9eb935481c343f72c743e70c6354aabebea34cd74baf3')
replace("tar.extractfile('reports/fresh-3-complete-declarations.txt')", "tar.extractfile('reports/fresh-4-complete-declarations.txt')")
replace('assert len(manager_reports) == 3','assert len(manager_reports) == 4')
replace("'module': 'TransferDeferredCountFlush01'", "'module': 'TransferDeferredBodyFailure01'")
replace('assert len(combined_reports) == 308','assert len(combined_reports) == 319')
replace('assert len(manager_selected) == 29','assert len(manager_selected) == 32')
replace("reference = {'deferred_count_flush':", "reference = {'deferred_body_failure':")
replace("'imported_complete_reports': 3", "'imported_complete_reports': 4")
replace("'complete_owned_modules': 29, 'inherited_complete_reports': 308", "'complete_owned_modules': 32, 'inherited_complete_reports': 319")
replace('Exact twenty-nine-module closure through concrete u64 current reads and whole deferred-flush count/effect composition, with all 308 inherited complete reports.', 'Exact thirty-two-module closure through both complete-Item body contexts and source-order primitive/index/delivery/deferred joins, with all 319 inherited complete reports.')
replace("add(stdout, 'reports/fresh-3-complete-declarations.txt'", "add(stdout, 'reports/fresh-6-complete-declarations.txt'")
s=s.replace('three exact max-count deferred walk/whole failure/empty retry proofs','installed source backend definition and five complete branch/reshape/whole nullifier admission proofs')
s=s.replace('complete twenty-nine-module first import root','complete thirty-two-module first import root')
s=s.replace('verified 308 inherited reports','verified 319 inherited reports')
s=s.replace('EXACT_MAX_COUNT_DERIVES_DEFERRED_FAILURE_QUEUE_DRAIN_AND_EMPTY_RETRY_QUALIFIED','WHOLE_TRANSFER_DELIVERY_DERIVES_ALL_INPUT_NULLIFIER_ADMISSION_QUALIFIED')
replace("'fresh_definition_audits': 0", "'fresh_definition_audits': 1")
replace("'fresh_theorem_audits': 3", "'fresh_theorem_audits': 5")
replace("'fresh_complete_public_audits': 3", "'fresh_complete_public_audits': 6")
replace("'inherited_complete_public_audits': 308", "'inherited_complete_public_audits': 319")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"""    'scope': mapping['scope'] + ' One definition and five handwritten theorems have complete original type/axiom reports. All input reader/pending observations and the exact bounded appended vector follow admission in the same successful enclosing action. Final object retention through later note writes and authenticated native/durable store correspondence remain separate. Added runtime bytes retain already-pinned ancestor source associations; hashes give identity, not semantic equivalence.'}
""".rstrip()+s[end:]
s=s.replace("'fresh_audits': 3, 'inherited_audits': 308", "'fresh_audits': 6, 'inherited_audits': 319")
needle="for row in mapping['runtime_sources']:"
assert s.count(needle)==1
associations="""runtime_rows = {row['path']: row for row in mapping['runtime_sources']}
for producer in ['transfer-nullifier-batch-source-20261011-02', 'transfer-raw-effects-source-20261011-04']:
    association_file = DIAG / producer / 'source-mapping.json'
    association_pin = pin(association_file)
    assert association_pin in plan['pins']
    association = json.loads(association_file.read_bytes())
    assert association['runtime_sha'] == mapping['runtime_sha']
    add(association_file, 'context/ancestor-source-associations/' + producer + '.json', 'unchanged source association already pinned in the qualified plan; not semantic proof')
    for row in association['runtime_sources']:
        assert pin(row['path']) == row
        assert row['path'] not in runtime_rows or runtime_rows[row['path']] == row
        runtime_rows[row['path']] = row
    for interface in association.get('interfaces', []):
        if interface not in mapping['interfaces']:
            mapping['interfaces'].append(interface)
mapping['runtime_sources'] = list(runtime_rows.values())
"""
s=s.replace(needle,associations+needle)
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':6,'inherited_reports':319,'owned_modules':32})
