"""Fresh successful successor sealer with both rejected whole attempts."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-fee-funding-delivery-endpoint-20261011-02/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-fee-funding-delivery-20261011-02'", "CURRENT = DIAG / 'transfer-fee-funding-delivery-20261011-03'")
s=s.replace('transfer-fee-funding-delivery-checkpoint-20261011-02','transfer-fee-funding-delivery-checkpoint-20261011-03')
s=s.replace("'rejected_attempts': 1", "'rejected_attempts': 2")
s=s.replace('The rejected predecessor remains immutable with zero credit. Its two solved-goal refinements and unused simplification are corrected only in this fresh successor; all four contracts are unchanged.', 'Both rejected predecessors remain immutable with zero whole-attempt credit. The proof-only successor closes the two True conjunctions and removes one unused simplification; all four contracts are unchanged.')
needle="add(ROOT / 'review.json', 'review.json'"
assert s.count(needle)==1
history="""rejected_second = DIAG / 'transfer-fee-funding-delivery-20261011-02'
second_events = [json.loads(line) for line in (rejected_second / 'events.jsonl').read_text().splitlines()]
assert len(second_events) == 2 and second_events[-1]['result']['status'] == 'failed'
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json',
             'events.jsonl', 'handwritten/TransferFeeFundingDelivery01.lean', 'project/ShielddSecurity/TransferFeeFundingDelivery01.lean',
             'runs/01-TransferFeeFundingDelivery01/stdout.txt']:
    add(rejected_second / name, 'rejected-second-predecessor/' + name, 'immutable rejected second whole attempt; zero proof credit')
assert contracts(original) == contracts((rejected_second / ('handwritten/' + MODULE + '.lean')).read_text())
setup = DIAG / 'transfer-fee-funding-delivery-endpoint-20261011-02'
for name in ['prepare_assembly.py', 'assemble.py']:
    add(setup / name, 'unexecuted-assembly-setup/' + name, 'unexecuted predecessor sealer setup; no evidence or proof credit')
"""
s=s.replace(needle,history+needle)
s=s.replace("'status': 'LOCALLY_QUALIFIED_AND_FULLY_TRANSPORTED; PARENT_ACCEPTANCE_SEPARATE'", "'status': 'PARENT_ACCEPTED_9a80f89cb67879e3291c32508519fccb64ad608a'")
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':311,'owned_modules':30,'rejected_attempts':2,'rejected_credit':0})
