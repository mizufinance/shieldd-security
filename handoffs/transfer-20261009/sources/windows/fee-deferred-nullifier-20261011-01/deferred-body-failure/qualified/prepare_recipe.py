"""Fresh read-back correction; withdrawn 02 plan was never executed."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
PRIOR=DIAG/'transfer-deferred-body-failure-20261011-02'
assert not (ROOT/'prepare.py').exists() and not (PRIOR/'events.jsonl').exists()
s=(PRIOR/'prepare.py').read_text().replace('transfer-deferred-body-failure-owned-floor-20261011-02','transfer-deferred-body-failure-owned-floor-20261011-03')
needle="plan['pins'] += mapping['runtime_sources']"
assert s.count(needle)==1
s=s.replace(needle,"""withdrawn_setup = DIAG / 'transfer-deferred-body-failure-20261011-02'
plan['pins'] += [pin(withdrawn_setup / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'handwritten/TransferDeferredBodyFailure01.lean', 'project/ShielddSecurity/TransferDeferredBodyFailure01.lean']]
"""+needle)
s=s.replace('Proof-only successor fixes branch continuation layout and supplies reflexive rewritten height witness. All four contracts and guards unchanged; rejected predecessor remains zero-credit.', 'Proof-only branch layout and reflexive height witness successor; read-back removes four literal patch markers before execution. Rejected 01 and withdrawn unrun 02 are preserved with zero credit. All four contracts and guards unchanged.')
(ROOT/'prepare.py').write_text(s)
original=(PRIOR/'handwritten/TransferDeferredBodyFailure01.lean').read_text()
assert original.count('\n+')==4
lean=original.replace('\n+','\n')
def contracts(text):
    return {m.group(1):m.group(0).split(' :=',1)[0] for m in re.finditer(r'^(?:def|theorem) (\w+)[\s\S]*?(?=\n(?:def|theorem|set_option pp.all)|\Z)',text,re.M)}
assert contracts(lean)==contracts(original) and len(contracts(lean))==4
f=ROOT/'handwritten/TransferDeferredBodyFailure01.lean'; f.parent.mkdir()
f.write_bytes(lean.encode())
print({'fresh_audits':4,'rejected_01_credit':0,'withdrawn_unrun_02_credit':0,'contracts_unchanged':True})
