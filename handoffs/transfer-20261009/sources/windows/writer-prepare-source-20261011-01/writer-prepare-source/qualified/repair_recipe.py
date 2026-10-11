"""Normalize definitionally identical Option.bind notation and explicit existential call receipts."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
old=DIAG/'transfer-writer-prepare-source-20261011-01'
s=(old/'handwritten/TransferWriterPrepareSource01.lean').read_text()
changes=[
('backend.height state >>= fun actualHeight =>','(backend.height state).bind fun actualHeight =>'),
('TransferPreparedAcceptedSource01.prepare backend.store previous.nullifiers height blockId accepted >>= fun insertions =>','(TransferPreparedAcceptedSource01.prepare backend.store previous.nullifiers height blockId accepted).bind fun insertions =>'),
('backend.stageBoundary state insertions >>= fun staged =>','(backend.stageBoundary state insertions).bind fun staged =>'),
('backend.prepareApplication staged >>= fun root =>','(backend.prepareApplication staged).bind fun root =>'),
('congrArg some sameHeight, locked, rfl, rfl, rfl, exactFrozen.symm','congrArg some sameHeight, locked, stored, stage, application, exactFrozen.symm')]
for a,b in changes:
    assert s.count(a)==1,a
    s=s.replace(a,b)
p=ROOT/'handwritten/TransferWriterPrepareSource01.lean'; assert not p.exists(); p.parent.mkdir(); p.write_text(s)
recipe=(old/'prepare_recipe.py').read_text().replace('transfer-writer-prepare-source-owned-floor-20261011-01','transfer-writer-prepare-source-owned-floor-20261011-02')
anchor="(ROOT/'prepare.py').write_text(s)"; assert recipe.count(anchor)==1
insert="""anchor = \"plan['pins'] += mapping['runtime_sources']\"; assert s.count(anchor)==1
pos=s.index(anchor)
s=s[:pos]+\"failed_writer = DIAG / 'transfer-writer-prepare-source-20261011-01'\\nplan['pins'] += [pin(failed_writer / n) for n in ['prepare_recipe.py', 'prepare.py', 'plan.json', 'review.json', 'execute_bounded.py', 'source-mapping.json', 'events.jsonl', 'handwritten/TransferWriterPrepareSource01.lean', 'project/ShielddSecurity/TransferWriterPrepareSource01.lean', 'runs/01-TransferWriterPrepareSource01/stdout.txt']]\\nplan['pins'].append(pin(ROOT / 'repair_recipe.py'))\\n\"+s[pos:]
"""
recipe=recipe.replace(anchor,insert+anchor); (ROOT/'prepare_recipe.py').write_text(recipe)
print({'program_change':'definitionally identical bind notation','contract_changes':0,'rejected_proof_credit':0})
