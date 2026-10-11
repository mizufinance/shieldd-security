"""Seal qualified helper rename successor and full rejected parser history."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-pending-seal-source-endpoint-20261011-01/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-pending-seal-source-20261011-01'", "CURRENT = DIAG / 'transfer-pending-seal-source-20261011-02'")
s=s.replace('transfer-pending-seal-source-checkpoint-20261011-01','transfer-pending-seal-source-checkpoint-20261011-02')
needle="add(ROOT / 'review.json', 'review.json'"
assert s.count(needle)==1
history="""import re
failed = DIAG / 'transfer-pending-seal-source-20261011-01'
failed_plan = json.loads((failed / 'plan.json').read_bytes())
failed_events = [json.loads(line) for line in (failed / 'events.jsonl').read_text().splitlines()]
assert len(failed_events) == 2 and failed_events[-1]['result']['status'] == 'failed'
assert not (failed / ('project/ShielddSecurity/' + MODULE + '.olean')).exists()
old_source = (failed / ('handwritten/' + MODULE + '.lean')).read_text()
new_source = (CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()
assert re.sub(r'\\bseal\\b', 'sealOnce', old_source) == new_source
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl',
    'handwritten/' + MODULE + '.lean', 'project/ShielddSecurity/' + MODULE + '.lean', 'runs/01-' + MODULE + '/stdout.txt']:
    assert pin(failed / name) in plan['pins']
    add(failed / name, 'rejected-01/' + name, 'reserved Lean command parser predecessor; whole proof/control credit zero; original source/plan/diagnostics preserved')
stopped_sealer = DIAG / 'transfer-pending-seal-source-endpoint-20261011-01'
assert not (stopped_sealer / 'manifest.json').exists() and not (stopped_sealer / 'portable-windows-pending-seal-source-endpoint01.tar.xz').exists()
for name in ['prepare_assembly.py', 'assemble.py']:
    add(stopped_sealer / name, 'unexecuted-sealer-01/' + name, 'unexecuted predecessor sealer setup, zero proof/control credit')
review['rejected_attempts'] = 1
review['rejected_attempt'] = {'plan': pin(failed / 'plan.json'), 'compiler_result': failed_events[-1]['result'], 'proof_credit': 0, 'control_credit': 0,
    'successor_diff': 'Exactly reserved helper identifier seal renamed sealOnce; no proof/type/premise/conclusion weakening or new axioms.'}
dump(ROOT / 'review.json', review)
"""
s=s.replace(needle,history+needle)
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':13,'inherited_reports':412,'owned_modules':42,'failed_history':1})
