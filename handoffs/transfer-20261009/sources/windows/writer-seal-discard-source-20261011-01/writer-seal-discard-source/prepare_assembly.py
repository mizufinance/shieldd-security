"""Seal lint-clean successor; retained warning attempt and object identity have zero credit."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-writer-seal-discard-source-endpoint-20261011-01/assemble.py').read_text()
anchor="CURRENT = DIAG / 'transfer-writer-seal-discard-source-20261011-01'"; assert s.count(anchor)==1
s=s.replace(anchor,"CURRENT = DIAG / 'transfer-writer-seal-discard-source-20261011-02'")
s=s.replace('transfer-writer-seal-discard-source-checkpoint-20261011-01','transfer-writer-seal-discard-source-checkpoint-20261011-02')
anchor="mapping = json.loads((CURRENT / 'source-mapping.json').read_bytes())"; assert s.count(anchor)==1
extra="""add(CURRENT / 'repair_recipe.py', 'qualified/repair_recipe.py', 'remove unnecessary simpa only; all strict guards/contracts unchanged')
failed = DIAG / 'transfer-writer-seal-discard-source-20261011-01'
for name in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferWriterSealDiscardSource01.lean', 'project/ShielddSecurity/TransferWriterSealDiscardSource01.lean', 'runs/01-TransferWriterSealDiscardSource01/stdout.txt']:
    add(failed / name, 'rejected/attempt01/' + name, 'full strict-lint rejected original attempt; zero proof/native/control credit')
failed_object = failed / 'project/ShielddSecurity/TransferWriterSealDiscardSource01.olean'
if failed_object.exists():
    assert pin(failed_object) in plan['pins']
    dump(ROOT / 'rejected-object-identity.json', {'object': pin(failed_object), 'imported': False, 'proof_credit': 0, 'scope': 'Strict audit rejected warning output; identity only, never reused in the accepted closure.'})
    add(ROOT / 'rejected-object-identity.json', 'rejected/attempt01/object-identity.json', 'retained object identity only; no object bytes or proof credit')
stopped = DIAG / 'transfer-writer-seal-discard-source-endpoint-20261011-01'
for name in ['prepare_assembly.py', 'assemble.py']:
    add(stopped / name, 'rejected/stopped-sealer-setup01/' + name, 'unexecuted sealer setup; zero credit')
"""
s=s.replace(anchor,extra+anchor).replace("'rejected_attempts': 0", "'rejected_attempts': 1")
(ROOT/'assemble.py').write_text(s)
print({'fresh_successor':True,'rejected_attempts':1,'rejected_proof_credit':0})
