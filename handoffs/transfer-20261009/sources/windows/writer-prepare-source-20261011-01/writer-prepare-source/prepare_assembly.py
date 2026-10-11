"""Seal writer preparation successor with complete failed predecessor and stopped setup."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-writer-prepare-source-endpoint-20261011-01/assemble.py').read_text()
anchor="CURRENT = DIAG / 'transfer-writer-prepare-source-20261011-01'"; assert s.count(anchor)==1
s=s.replace(anchor,"CURRENT = DIAG / 'transfer-writer-prepare-source-20261011-02'")
s=s.replace('transfer-writer-prepare-source-checkpoint-20261011-01','transfer-writer-prepare-source-checkpoint-20261011-02')
anchor="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"; assert s.count(anchor)==1
extra="""add(CURRENT / 'repair_recipe.py', 'qualified/repair_recipe.py', 'definitionally identical Option.bind notation and explicit existential receipts; contracts unchanged')
failed = DIAG / 'transfer-writer-prepare-source-20261011-01'
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferWriterPrepareSource01.lean', 'project/ShielddSecurity/TransferWriterPrepareSource01.lean', 'runs/01-TransferWriterPrepareSource01/stdout.txt']:
    add(failed / name, 'rejected/attempt01/' + name, 'full failed original attempt; zero proof/native/control credit')
stopped = DIAG / 'transfer-writer-prepare-source-endpoint-20261011-01'
for name in ['prepare_assembly.py', 'assemble.py']:
    add(stopped / name, 'rejected/stopped-sealer-setup01/' + name, 'unexecuted sealer setup; zero credit')
"""
s=s.replace(anchor,extra+anchor).replace("'rejected_attempts': 0", "'rejected_attempts': 1")
(ROOT/'assemble.py').write_text(s)
print({'fresh_successor':True,'rejected_attempts':1,'rejected_proof_credit':0})
