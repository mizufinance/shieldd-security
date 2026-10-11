"""Proof-only branch layout/rewritten height witness successor."""
from pathlib import Path
import json, re
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
PRIOR=DIAG/'transfer-deferred-body-failure-20261011-01'
assert not (ROOT/'prepare.py').exists()
events=[json.loads(x) for x in (PRIOR/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='failed'
s=(PRIOR/'prepare.py').read_text().replace('transfer-deferred-body-failure-owned-floor-20261011-01','transfer-deferred-body-failure-owned-floor-20261011-02')
needle="plan['pins'] += mapping['runtime_sources']"
assert s.count(needle)==1
s=s.replace(needle,"""rejected_body = DIAG / 'transfer-deferred-body-failure-20261011-01'
plan['pins'] += [pin(rejected_body / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'handwritten/TransferDeferredBodyFailure01.lean',
    'project/ShielddSecurity/TransferDeferredBodyFailure01.lean', 'runs/01-TransferDeferredBodyFailure01/stdout.txt']]
"""+needle)
s=s.replace('Fresh finite both-context deferred body/index failure/empty retry composition; qualified ancestors and guards unchanged.', 'Proof-only successor fixes branch continuation layout and supplies reflexive rewritten height witness. All four contracts and guards unchanged; rejected predecessor remains zero-credit.')
(ROOT/'prepare.py').write_text(s)
original=(PRIOR/'handwritten/TransferDeferredBodyFailure01.lean').read_text()
lean=original
# Tactic alternatives put exact on its own indented line.
lean=lean.replace('  | ordinary => exact ', '  | ordinary =>\n+    exact ')
lean=lean.replace('  | feeFunding => exact ', '  | feeFunding =>\n+    exact ')
lean=lean.replace('      | ordinary => exact ', '      | ordinary =>\n+        exact ')
lean=lean.replace('      | feeFunding => exact ', '      | feeFunding =>\n+        exact ')
# The broad two-space replacements include nested cases; correct their new line.
lean=lean.replace('      | ordinary =>\n+    exact ', '      | ordinary =>\n+        exact ')
lean=lean.replace('      | feeFunding =>\n+    exact ', '      | feeFunding =>\n+        exact ')
assert lean.count('⟨deliveryHeight, heightRead⟩')==1
lean=lean.replace('⟨deliveryHeight, heightRead⟩','⟨deliveryHeight, rfl⟩')
def contracts(text):
    return {m.group(1):m.group(0).split(' :=',1)[0] for m in re.finditer(r'^(?:def|theorem) (\w+)[\s\S]*?(?=\n(?:def|theorem|set_option pp.all)|\Z)',text,re.M)}
assert contracts(lean)==contracts(original) and len(contracts(lean))==4
f=ROOT/'handwritten/TransferDeferredBodyFailure01.lean'; f.parent.mkdir()
f.write_bytes(lean.encode())
print({'fresh_audits':4,'rejected_credit':0,'contracts_unchanged':True})
