"""Seal qualified successor with failed history and full Readback association."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-whole-durable-readback-endpoint-20261011-01/assemble.py').read_text()
s=s.replace("CURRENT = DIAG / 'transfer-whole-durable-readback-20261011-01'", "CURRENT = DIAG / 'transfer-whole-durable-readback-20261011-02'")
s=s.replace('transfer-whole-durable-readback-checkpoint-20261011-01','transfer-whole-durable-readback-checkpoint-20261011-02')
needle="add(ROOT / 'review.json', 'review.json'"
assert s.count(needle)==1
history="""failed = DIAG / 'transfer-whole-durable-readback-20261011-01'
failed_plan = json.loads((failed / 'plan.json').read_bytes())
failed_events = [json.loads(line) for line in (failed / 'events.jsonl').read_text().splitlines()]
assert len(failed_events) == 2 and failed_events[-1]['result']['status'] == 'failed'
assert not (failed / ('project/ShielddSecurity/' + MODULE + '.olean')).exists()
old_source = (failed / ('handwritten/' + MODULE + '.lean')).read_text()
new_source = (CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()
expected = old_source.replace('exact ⟨store, boundary, response, reader, boundaryRead, locked, checked, unspent⟩',
    'exact ⟨store, boundary, response, rfl, rfl, rfl, checked, unspent⟩')
expected = expected.replace('∃ store boundary response,', '∃ (store : Store) (boundary : Boundary) (response : Status),')
assert expected == new_source
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl',
    'handwritten/' + MODULE + '.lean', 'project/ShielddSecurity/' + MODULE + '.lean', 'runs/01-' + MODULE + '/stdout.txt']:
    row = pin(failed / name)
    assert row in plan['pins']
    add(failed / name, 'rejected-01/' + name, 'failed elaboration predecessor, whole proof/control credit zero; no admitted source mutated')
stopped_sealer = DIAG / 'transfer-whole-durable-readback-endpoint-20261011-01'
assert not (stopped_sealer / 'manifest.json').exists() and not (stopped_sealer / 'portable-windows-whole-durable-readback-endpoint01.tar.xz').exists()
for name in ['prepare_assembly.py', 'assemble.py']:
    add(stopped_sealer / name, 'unexecuted-sealer-01/' + name, 'unexecuted predecessor sealer setup, zero proof/control credit')
readback = DIAG / 'transfer-readback-recovery-publication-20261010-02'
for name in ['project/ShielddSecurity/TransferReadback.lean', 'plan.json', 'execute_bounded.py', 'events.jsonl',
    'source-mapping.json', 'runs/01-TransferReadback/stdout.txt']:
    row = pin(readback / name)
    assert row in plan['pins']
    add(readback / name, 'readback-ancestor/' + name, 'original seventeen-report Readback source/plan/runner/events/raw type and axiom association; no replay credit')
assert pin(readback / 'project/ShielddSecurity/TransferReadback.olean') == readback_events[1]['result']['objects'][0]
review['rejected_attempts'] = 1
review['rejected_attempt'] = {'plan': pin(failed / 'plan.json'), 'compiler_result': failed_events[-1]['result'],
    'proof_credit': 0, 'control_credit': 0, 'successor_diff': 'Only reflexivity for rewritten case goals and explicit intended Store/Boundary/Status existential type annotations; no premises or conclusions weakened.'}
review['readback_ancestor'] = {'module': 'TransferReadback', 'source': readback_plan['targets'][0]['source'],
    'object': readback_events[1]['result']['objects'][0], 'stdout': readback_events[1]['result']['stdout'], 'complete_reports': 17,
    'archive': pin(readback_archive), 'transport': 'windows-readback-publication-endpoint01', 'fresh_replay_credit': 0}
dump(ROOT / 'review.json', review)
"""
s=s.replace(needle,history+needle)
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':11,'inherited_reports':368,'owned_modules':37,'failed_history':1,'full_readback_association':True})
