"""Seal the fresh overlay-proof successor with immutable failed history."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent; DIAG=ROOT.parent
assert not (ROOT/'assemble.py').exists()
s=(DIAG/'transfer-deferred-count-walk-endpoint-20261011-01/assemble.py').read_text()
s=s.replace('transfer-deferred-count-walk-20261011-01','transfer-deferred-count-walk-20261011-02')
s=s.replace('transfer-deferred-count-walk-checkpoint-20261011-01','transfer-deferred-count-walk-checkpoint-20261011-02')
before="for name in ['prepare-rejected-owned-count.py','prepare_recipe-rejected-owned-count.py']:\n    add(CURRENT / name, 'rejected-preparation/' + name, 'owned module census correction before any plan or Lean admission; zero proof credit')"
assert s.count(before)==1
extra="""REJECTED = DIAG / 'transfer-deferred-count-walk-20261011-01'
history = [json.loads(x) for x in (REJECTED / 'events.jsonl').read_text().splitlines()]
assert len(history) == 2 and history[-1]['result']['status'] == 'failed'
import re
old = (REJECTED / ('handwritten/' + MODULE + '.lean')).read_text()
new = (CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()
def signatures(text):
    return [text[match.start():text.index(' :=',match.start())] for match in re.finditer(r'^theorem ',text,re.M)]
assert signatures(old) == signatures(new) and len(signatures(new)) == 3
assert old[old.index('def queueWriter'):old.index('theorem ')] == new[new.index('def queueWriter'):new.index('theorem ')]
for name in ['prepare.py','prepare_recipe.py','plan.json','review.json','source-mapping.json','events.jsonl','execute_bounded.py','handwritten/' + MODULE + '.lean','project/ShielddSecurity/' + MODULE + '.lean','runs/01-' + MODULE + '/stdout.txt']:
    add(REJECTED / name, 'rejected-01/' + name, 'original compiler failure; whole attempt zero credit')
for name in ['prepare-rejected-owned-count.py','prepare_recipe-rejected-owned-count.py']:
    add(REJECTED / name, 'rejected-preparation/' + name, 'owned census correction before plan or Lean admission; zero proof credit')
"""
s=s.replace(before,extra)
s=s.replace("'rejected_attempts': 0, 'rejected_proof_credit': 0", "'rejected_attempts': 1, 'rejected_proof_credit': 0")
s=s.replace('Four public declarations have full original reports.', 'Successful fresh successor supplies all four complete original type/axiom reports. One queue-writer definition and three theorem conclusions are unchanged; only overlay normalization in the step proof was repaired. Rejected compiler attempt receives zero credit.')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':4,'inherited_reports':301,'owned_modules':27,'rejected_compiler_credit':0,'rejected_preparation_credit':0})
