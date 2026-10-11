"""Close the two simplified True conjunctions; retain both failed attempts."""
from pathlib import Path
import json, re
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
PRIOR=DIAG/'transfer-fee-funding-delivery-20261011-02'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(x) for x in (PRIOR/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='failed'
s=(PRIOR/'prepare.py').read_text().replace('transfer-fee-funding-delivery-owned-floor-20261011-02','transfer-fee-funding-delivery-owned-floor-20261011-03')
needle="plan['pins'] += mapping['runtime_sources']"
assert s.count(needle)==1
history="""rejected_second = DIAG / 'transfer-fee-funding-delivery-20261011-02'
plan['pins'] += [pin(rejected_second / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferFeeFundingDelivery01.lean',
    'project/ShielddSecurity/TransferFeeFundingDelivery01.lean', 'runs/01-TransferFeeFundingDelivery01/stdout.txt']]
"""
s=s.replace(needle,history+needle)
s=s.replace('Proof-only successor removes solved-goal refinements and one unused simplification. All definitions/theorem contracts and guards unchanged; rejected predecessor has zero proof credit.', 'Proof-only successor closes the two True conjunctions left by simplification. All definitions/theorem contracts and guards unchanged; both rejected predecessors have zero proof credit.')
(ROOT/'prepare.py').write_text(s)
original=(PRIOR/'handwritten/TransferFeeFundingDelivery01.lean').read_text()
lean=original
for before in ['simp only [executeBound, TransferCapabilitySource01.execute, observed]',
               'simp only [executeBound, TransferCapabilitySource01.execute, observed, if_neg matched]']:
    assert lean.count(before)==1
    lean=lean.replace(before,before+'; exact ⟨True.intro, True.intro⟩')
def contracts(text):
    return {m.group(1):m.group(0).split(' :=',1)[0] for m in re.finditer(r'^(?:def|theorem) (\w+)[\s\S]*?(?=\n(?:def|theorem|set_option pp.all)|\Z)',text,re.M)}
assert contracts(lean)==contracts(original) and len(contracts(lean))==4
f=ROOT/'handwritten/TransferFeeFundingDelivery01.lean'; f.parent.mkdir()
f.write_bytes(lean.encode())
print({'fresh_audits':4,'rejected_attempts':2,'rejected_credit':0,'contracts_unchanged':True})
