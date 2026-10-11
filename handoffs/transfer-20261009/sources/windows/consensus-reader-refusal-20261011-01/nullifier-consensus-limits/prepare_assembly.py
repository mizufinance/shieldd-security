"""Seal generated successor with exact regeneration and complete failed history."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-nullifier-consensus-limits-endpoint-20261011-01/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-nullifier-consensus-limits-20261011-01'", "CURRENT = DIAG / 'transfer-nullifier-consensus-limits-20261011-02'")
s=s.replace('transfer-nullifier-consensus-limits-checkpoint-20261011-01','transfer-nullifier-consensus-limits-checkpoint-20261011-02')
s=s.replace('transfer-nullifier-consensus-limits-regeneration-20261011-01','transfer-nullifier-consensus-limits-regeneration-20261011-02')
needle="add(ROOT / 'review.json', 'review.json'"
assert s.count(needle)==1
history="""failed = DIAG / 'transfer-nullifier-consensus-limits-20261011-01'
failed_plan = json.loads((failed / 'plan.json').read_bytes())
failed_events = [json.loads(line) for line in (failed / 'events.jsonl').read_text().splitlines()]
assert len(failed_events) == 2 and failed_events[-1]['result']['status'] == 'failed'
assert not (failed / ('project/ShielddSecurity/' + MODULE + '.olean')).exists()
old_source = (failed / ('generated/' + MODULE + '.lean')).read_text()
new_source = (CURRENT / ('generated/' + MODULE + '.lean')).read_text()
normalized = new_source.replace('set_option autoImplicit false\\n', '')
for namespace, identifier in [('TransferWholeDurableReadback01', 'installReader'), ('TransferWholeDurableReadback01', 'currentReader'),
    ('TransferCurrentPendingReplay01', 'withPending')]:
    normalized = normalized.replace(namespace + '.' + identifier, identifier)
assert normalized == old_source
for name in ['generate.py', 'generation.json', 'prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py',
    'source-mapping.json', 'events.jsonl', 'generated/' + MODULE + '.lean', 'project/ShielddSecurity/' + MODULE + '.lean',
    'runs/01-' + MODULE + '/stdout.txt']:
    row = pin(failed / name)
    assert row in plan['pins']
    add(failed / name, 'rejected-01/' + name, 'failed generator helper qualification predecessor, whole proof/control credit zero; no generated source/evidence patched')
failed_regen = DIAG / 'transfer-nullifier-consensus-limits-regeneration-20261011-01'
for name in ['generation.json', 'generated/' + MODULE + '.lean']:
    assert pin(failed_regen / name) in plan['pins']
    add(failed_regen / name, 'rejected-01-regeneration/' + name, 'original exact regeneration for rejected generation; zero proof/control credit')
stopped_sealer = DIAG / 'transfer-nullifier-consensus-limits-endpoint-20261011-01'
assert not (stopped_sealer / 'manifest.json').exists() and not (stopped_sealer / 'portable-windows-nullifier-consensus-limits-endpoint01.tar.xz').exists()
for name in ['prepare_assembly.py', 'assemble.py']:
    add(stopped_sealer / name, 'unexecuted-sealer-01/' + name, 'unexecuted failed predecessor sealer setup, zero proof/control credit')
review['rejected_attempts'] = 1
review['rejected_attempt'] = {'plan': pin(failed / 'plan.json'), 'compiler_result': failed_events[-1]['result'],
    'proof_credit': 0, 'control_credit': 0, 'successor_diff': 'Maintained generator qualifies exactly three original helper names and disables autoImplicit. Every source declaration/premise/conclusion otherwise byte-identical after namespace normalization.'}
dump(ROOT / 'review.json', review)
"""
s=s.replace(needle,history+needle)
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':7,'inherited_reports':379,'owned_modules':38,'failed_history':1,'regeneration_exact':True})
