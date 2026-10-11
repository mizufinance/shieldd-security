"""Seal the qualified successor with failed and withdrawn history."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-deferred-body-failure-endpoint-20261011-01/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-deferred-body-failure-20261011-01'", "CURRENT = DIAG / 'transfer-deferred-body-failure-20261011-03'")
s=s.replace('transfer-deferred-body-failure-checkpoint-20261011-01','transfer-deferred-body-failure-checkpoint-20261011-03')
s=s.replace("'rejected_attempts': 0", "'rejected_attempts': 1, 'withdrawn_unrun_plans': 1")
s=s.replace('The definition and all three handwritten theorems have complete original type/axiom reports.', 'The definition and all three handwritten theorems have complete original type/axiom reports. Failed 01 and withdrawn unrun 02 retain zero credit; all four definition/theorem contracts are unchanged by the branch layout, reflexive height witness and preparation read-back corrections.')
needle="add(ROOT / 'review.json', 'review.json'"
assert s.count(needle)==1
history="""rejected = DIAG / 'transfer-deferred-body-failure-20261011-01'
failed_events = [json.loads(line) for line in (rejected / 'events.jsonl').read_text().splitlines()]
assert len(failed_events) == 2 and failed_events[-1]['result']['status'] == 'failed'
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json',
             'events.jsonl', 'handwritten/TransferDeferredBodyFailure01.lean', 'project/ShielddSecurity/TransferDeferredBodyFailure01.lean',
             'runs/01-TransferDeferredBodyFailure01/stdout.txt']:
    add(rejected / name, 'rejected-predecessor/' + name, 'immutable failed whole attempt; zero proof credit')
withdrawn = DIAG / 'transfer-deferred-body-failure-20261011-02'
assert not (withdrawn / 'events.jsonl').exists() and not (withdrawn / ('project/ShielddSecurity/' + MODULE + '.olean')).exists()
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json',
             'handwritten/TransferDeferredBodyFailure01.lean', 'project/ShielddSecurity/TransferDeferredBodyFailure01.lean']:
    add(withdrawn / name, 'withdrawn-unrun-setup/' + name, 'withdrawn unrun preparation with literal patch markers; zero credit')
import re
def contracts(text):
    return {match.group(1): match.group(0).split(' :=', 1)[0] for match in re.finditer(
        r'^(?:def|theorem) (\\w+)[\\s\\S]*?(?=\\n(?:def|theorem|set_option pp.all)|\\Z)', text, re.M)}
original = (rejected / ('handwritten/' + MODULE + '.lean')).read_text()
assert len(contracts(original)) == 4
for directory in [CURRENT, withdrawn]:
    assert contracts(original) == contracts((directory / ('handwritten/' + MODULE + '.lean')).read_text())
setup = DIAG / 'transfer-deferred-body-failure-endpoint-20261011-01'
for name in ['prepare_assembly.py', 'assemble.py']:
    add(setup / name, 'unexecuted-assembly-setup/' + name, 'unexecuted predecessor sealer setup; no evidence or proof credit')
"""
s=s.replace(needle,history+needle)
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':315,'owned_modules':31,'rejected_attempts':1,'withdrawn_unrun_plans':1})
