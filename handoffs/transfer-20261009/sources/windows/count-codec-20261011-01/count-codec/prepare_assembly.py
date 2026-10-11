"""Seal a fresh successful successor while carrying the entire rejected attempt."""
from pathlib import Path
ROOT=Path(__file__).resolve().parent
DIAG=ROOT.parent
assert not (ROOT/'portable-windows-index-count-codec-endpoint01.tar.xz').exists()
s=(DIAG/'transfer-index-count-codec-endpoint-20261011-01/assemble.py').read_text()
s=s.replace('transfer-index-count-codec-20261011-01','transfer-index-count-codec-20261011-02')
s=s.replace('transfer-index-count-codec-checkpoint-20261011-01','transfer-index-count-codec-checkpoint-20261011-02')
before="add(ROOT / 'prepare_assembly.py', 'prepare_assembly.py', 'exact assembly derivation source')"
assert s.count(before)==1
extra="""REJECTED = DIAG / 'transfer-index-count-codec-20261011-01'
history = [json.loads(x) for x in (REJECTED / 'events.jsonl').read_text().splitlines()]
assert len(history) == 2 and history[-1]['result']['status'] == 'failed'
import re
old_lean = (REJECTED / ('handwritten/' + MODULE + '.lean')).read_text()
new_lean = (CURRENT / ('handwritten/' + MODULE + '.lean')).read_text()
def signatures(text):
    result = []
    for match in re.finditer(r'^theorem ', text, re.M):
        end = text.index(' :=', match.start())
        result.append(text[match.start():end])
    return result
assert signatures(old_lean) == signatures(new_lean) and len(signatures(new_lean)) == 10
assert re.findall(r'^def .*?(?=\\n(?:def|theorem)|\\nset_option|\\nend)', old_lean, re.M|re.S) == re.findall(r'^def .*?(?=\\n(?:def|theorem)|\\nset_option|\\nend)', new_lean, re.M|re.S)
for name in ['prepare.py', 'prepare_recipe.py', 'plan.json', 'review.json', 'source-mapping.json', 'events.jsonl', 'execute_bounded.py', 'handwritten/' + MODULE + '.lean', 'project/ShielddSecurity/' + MODULE + '.lean', 'runs/01-' + MODULE + '/stdout.txt']:
    add(REJECTED / name, 'rejected-01/' + name, 'complete original compiler failure; zero credit')
"""
s=s.replace(before,extra+'\n'+before)
s=s.replace("'rejected_attempts': 0, 'rejected_proof_credit': 0", "'rejected_attempts': 1, 'rejected_proof_credit': 0")
s=s.replace('All codec definitions and ten mathematical proofs have complete conclusions and axiom audits.', 'Successful fresh successor audits all five unchanged codec definitions and ten unchanged theorem conclusions. Rejected first compiler attempt is retained with zero credit; reserved binder, multiplication orientation and dependent-if proof were repaired only in fresh handwritten source.')
(ROOT/'assemble.py').write_text(s)
print({'fresh_reports':15,'inherited_reports':256,'owned_modules':22,'rejected_attempt_credit':0})
