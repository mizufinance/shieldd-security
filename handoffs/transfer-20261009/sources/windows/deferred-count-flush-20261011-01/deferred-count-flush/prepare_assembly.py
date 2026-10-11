"""Seal fresh three-theorem flush successor and full rejected history."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-deferred-count-flush-endpoint-20261011-01/assemble.py').read_text()
s=s.replace('transfer-deferred-count-flush-20261011-01','transfer-deferred-count-flush-20261011-02')
s=s.replace('transfer-deferred-count-flush-checkpoint-20261011-01','transfer-deferred-count-flush-checkpoint-20261011-02')
before="add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact assembly derivation source')"
assert s.count(before)==1
extra="""REJECTED = DIAG / 'transfer-deferred-count-flush-20261011-01'
history = [json.loads(x) for x in (REJECTED / 'events.jsonl').read_text().splitlines()]
assert len(history) == 2 and history[-1]['result']['status'] == 'failed'
import re
old = (REJECTED / ('handwritten/' + MODULE + '.lean')).read_text()
new = (CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()
def signatures(text):
    return [text[match.start():text.index(' :=',match.start())] for match in re.finditer(r'^theorem ',text,re.M)]
assert signatures(old) == signatures(new) and len(signatures(new)) == 3
for name in ['prepare.py','prepare_recipe.py','plan.json','review.json','source-mapping.json','events.jsonl','execute_bounded.py','handwritten/' + MODULE + '.lean','project/ShielddSecurity/' + MODULE + '.lean','runs/01-' + MODULE + '/stdout.txt']:
    add(REJECTED / name, 'rejected-01/' + name, 'original compiler error and warning; whole attempt zero credit')
"""
s=s.replace(before,extra+'\n'+before)
s=s.replace("'rejected_attempts': 0, 'rejected_proof_credit': 0", "'rejected_attempts': 1, 'rejected_proof_credit': 0")
s=s.replace('All three handwritten theorems have complete original conclusion/axiom reports.', 'Successful fresh successor supplies all three complete original conclusion/axiom reports. All theorem signatures equal the rejected predecessor; only the redundant simplification was removed, with all warnings still fatal. The original compiler error/warning attempt receives zero credit.')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':3,'inherited_reports':305,'owned_modules':28,'rejected_credit':0})
