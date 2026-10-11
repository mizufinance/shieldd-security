"""Fresh sealing successor; preserve full failed attempt and stopped sealer setup."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-prepared-accepted-source-endpoint-20261011-01'
assert not (ROOT/'assemble.py').exists()
recipe=(old/'prepare_assembly.py').read_text()
# Execute the unchanged first recipe with a local replacement of its final write,
# then specialize the resulting assembly text without touching the old attempt.
anchor="(ROOT/'assemble.py').write_text(s)"
assert recipe.count(anchor)==1
recipe=recipe.replace(anchor,'')
scope={'__file__':str(ROOT/'prepare_assembly.py')}
exec(compile(recipe,str(old/'prepare_assembly.py'),'exec'),scope)
s=scope['s']
assert s.count("CURRENT = DIAG / 'transfer-prepared-accepted-source-20261011-01'")==1
s=s.replace("CURRENT = DIAG / 'transfer-prepared-accepted-source-20261011-01'", "CURRENT = DIAG / 'transfer-prepared-accepted-source-20261011-02'")
s=s.replace('transfer-prepared-accepted-source-checkpoint-20261011-01','transfer-prepared-accepted-source-checkpoint-20261011-02')
anchor="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"
assert s.count(anchor)==1
extra="""add(CURRENT / 'repair_recipe.py', 'qualified/repair_recipe.py', 'explicit gate decider and case reflexivity repairs; no contract changes')
failed = DIAG / 'transfer-prepared-accepted-source-20261011-01'
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferPreparedAcceptedSource01.lean', 'project/ShielddSecurity/TransferPreparedAcceptedSource01.lean', 'runs/01-TransferPreparedAcceptedSource01/stdout.txt']:
    add(failed / name, 'rejected/attempt01/' + name, 'full failed attempt; zero proof/native/control credit')
stopped = DIAG / 'transfer-prepared-accepted-source-endpoint-20261011-01'
for name in ['prepare_assembly.py', 'assemble.py']:
    add(stopped / name, 'rejected/stopped-sealer-setup01/' + name, 'unexecuted sealer setup; zero credit')
"""
s=s.replace(anchor,extra+anchor)
s=s.replace("'rejected_attempts': 0", "'rejected_attempts': 1")
(ROOT/'assemble.py').write_text(s)
print({'fresh_successor':True,'rejected_attempts':1,'rejected_proof_credit':0})
