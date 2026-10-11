"""Fresh proof-only successor; preserve every rejected input and contract."""
from pathlib import Path
import json, re
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
PRIOR=DIAG/'transfer-fee-funding-delivery-20261011-01'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(x) for x in (PRIOR/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='failed'
s=(PRIOR/'prepare.py').read_text().replace('transfer-fee-funding-delivery-owned-floor-20261011-01','transfer-fee-funding-delivery-owned-floor-20261011-02')
s=s.replace("plan['source_repairs'] = 'Fresh finite FeeFunding source/body/whole-delivery composition; inherited proofs and guards unchanged.'", "plan['source_repairs'] = 'Proof-only successor removes solved-goal refinements and one unused simplification. All definitions/theorem contracts and guards unchanged; rejected predecessor has zero proof credit.'")
needle="plan['pins'] += mapping['runtime_sources']"
assert s.count(needle)==1
history="""rejected = DIAG / 'transfer-fee-funding-delivery-20261011-01'
plan['pins'] += [pin(rejected / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferFeeFundingDelivery01.lean',
    'project/ShielddSecurity/TransferFeeFundingDelivery01.lean', 'runs/01-TransferFeeFundingDelivery01/stdout.txt']]
"""
s=s.replace(needle,history+needle)
(ROOT/'prepare.py').write_text(s)
original=(PRIOR/'handwritten/TransferFeeFundingDelivery01.lean').read_text()
lean=original
assert lean.count('; exact ⟨rfl, rfl⟩')==2
lean=lean.replace('; exact ⟨rfl, rfl⟩','')
before='    simp only [dispatch, TransferCapabilitySource01.isOrdinary, TransferRawEffectsSource01.executeTransfer,\n      ↓reduceIte, next, result, TransferCapabilitySource01.liftRaw] at success'
after=before.replace('TransferCapabilitySource01.isOrdinary, ','')
assert lean.count(before)==1
lean=lean.replace(before,after)
def contracts(text):
    return {m.group(1):m.group(0).split(' :=',1)[0] for m in re.finditer(r'^(?:def|theorem) (\w+)[\s\S]*?(?=\n(?:def|theorem|set_option pp.all)|\Z)',text,re.M)}
assert contracts(lean)==contracts(original) and len(contracts(lean))==4
f=ROOT/'handwritten/TransferFeeFundingDelivery01.lean'; f.parent.mkdir()
f.write_bytes(lean.encode())
print({'fresh_audits':4,'rejected_predecessor_credit':0,'definition_and_theorem_contracts_unchanged':True})
