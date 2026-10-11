"""Seal FeeFunding whole delivery, exact ancestry and zero-credit rejection."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-deferred-max-count-endpoint-20261011-01/assemble.py').read_text()
def replace(a,b):
    global s
    assert s.count(a)==1,a
    s=s.replace(a,b)
s=s.replace('transfer-deferred-max-count-20261011-01','transfer-fee-funding-delivery-20261011-02')
s=s.replace('transfer-deferred-max-count-checkpoint-20261011-01','transfer-fee-funding-delivery-checkpoint-20261011-02')
s=s.replace('deferred-max-count-endpoint','fee-funding-delivery-endpoint')
replace("MODULE = 'TransferDeferredMaxCount01'", "MODULE = 'TransferFeeFundingDelivery01'")
replace('assert len(fresh) == 3','assert len(fresh) == 4')
replace("assert pool['objects'] == 29 and len(pool['inherited_public_reports']) == 308", "assert pool['objects'] == 30 and len(pool['inherited_public_reports']) == 311")
replace("manager_endpoint = DIAG / 'transfer-deferred-count-flush-endpoint-20261011-02'", "manager_endpoint = DIAG / 'transfer-deferred-max-count-endpoint-20261011-01'")
replace("manager_archive = manager_endpoint / 'portable-windows-deferred-count-flush-endpoint01.tar.xz'", "manager_archive = manager_endpoint / 'portable-windows-deferred-max-count-endpoint01.tar.xz'")
replace('3ebee7fe7c088e3e566ec68b8e52e33f5963b1c735f9ea0903dd4235f2821ec7','ce328595c82ae0b19e85128606f2c17aac51f726659cda17786a70c3b0f2e638')
replace("'module': 'TransferDeferredCountFlush01'", "'module': 'TransferDeferredMaxCount01'")
replace('assert len(combined_reports) == 308','assert len(combined_reports) == 311')
replace('assert len(manager_selected) == 29','assert len(manager_selected) == 30')
replace("reference = {'deferred_count_flush':", "reference = {'deferred_max_count':")
replace("'complete_owned_modules': 29, 'inherited_complete_reports': 308", "'complete_owned_modules': 30, 'inherited_complete_reports': 311")
replace('Exact twenty-nine-module closure through concrete u64 current reads and whole deferred-flush count/effect composition, with all 308 inherited complete reports.', 'Exact thirty-module closure through concrete u64 current reads and complete Ordinary/deferred source joins, with all 311 inherited complete reports.')
# This ancestor still has three reports; only the fresh target has four.
replace("add(stdout, 'reports/fresh-3-complete-declarations.txt'", "add(stdout, 'reports/fresh-4-complete-declarations.txt'")
s=s.replace('three exact max-count deferred walk/whole failure/empty retry proofs', 'FeeFunding source definition and three body/current-read/whole-delivery proofs')
s=s.replace('complete twenty-nine-module first import root', 'complete thirty-module first import root')
s=s.replace('verified 308 inherited reports', 'verified 311 inherited reports')
s=s.replace('EXACT_MAX_COUNT_DERIVES_DEFERRED_FAILURE_QUEUE_DRAIN_AND_EMPTY_RETRY_QUALIFIED', 'FEE_FUNDING_WHOLE_DELIVERY_DERIVES_REEXTRACTION_CURRENT_READS_CODEC_AND_EFFECTS_QUALIFIED')
replace("'fresh_definition_audits': 0", "'fresh_definition_audits': 1")
replace("'fresh_complete_public_audits': 3", "'fresh_complete_public_audits': 4")
replace("'inherited_complete_public_audits': 308", "'inherited_complete_public_audits': 311")
replace("'rejected_attempts': 0", "'rejected_attempts': 1")
start=s.index("    'scope': mapping['scope'] + "); end=s.index("\ndump(ROOT / 'review.json', review)",start)
s=s[:start]+"""    'scope': mapping['scope'] + ' One definition and all three theorems have complete original type/axiom reports. The rejected predecessor remains immutable with zero credit. Its two solved-goal refinements and unused simplification are corrected only in this fresh successor; all four contracts are unchanged. Native genuine controls remain separate and unrun.'}
""".rstrip()+s[end:]
s=s.replace("'fresh_audits': 3, 'inherited_audits': 308", "'fresh_audits': 4, 'inherited_audits': 311")
needle="add(ROOT / 'review.json', 'review.json'"
assert s.count(needle)==1
history="""rejected = DIAG / 'transfer-fee-funding-delivery-20261011-01'
rejected_events = [json.loads(line) for line in (rejected / 'events.jsonl').read_text().splitlines()]
assert len(rejected_events) == 2 and rejected_events[-1]['result']['status'] == 'failed'
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json',
             'events.jsonl', 'handwritten/TransferFeeFundingDelivery01.lean', 'project/ShielddSecurity/TransferFeeFundingDelivery01.lean',
             'runs/01-TransferFeeFundingDelivery01/stdout.txt']:
    add(rejected / name, 'rejected-predecessor/' + name, 'immutable rejected whole attempt; zero proof credit')
import re
def contracts(text):
    return {match.group(1): match.group(0).split(' :=', 1)[0] for match in re.finditer(
        r'^(?:def|theorem) (\\w+)[\\s\\S]*?(?=\\n(?:def|theorem|set_option pp.all)|\\Z)', text, re.M)}
original = (rejected / ('handwritten/' + MODULE + '.lean')).read_text()
successor = (CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()
assert contracts(original) == contracts(successor) and len(contracts(original)) == 4
"""
s=s.replace(needle,history+needle)
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':311,'owned_modules':30,'rejected_proof_credit':0})
