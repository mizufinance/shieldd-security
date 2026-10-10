"""Prepare the six maintained secant/tangent modules from qualified imports."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-10/prepare.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == '67d3b7b1e7a4c571b752522f8659b9123556b01df4f0618492c5941a9d733853'
text = prior.read_text()
start = text.index('MODULES = ')
end = text.index('\n\ndef pin', start)
text = text[:start] + "MODULES = ['EdwardsSecantPolynomials01', 'EdwardsSecantRational01', 'ConcreteSecantAddition01',\n           'EdwardsTangentPolynomials01', 'EdwardsTangentRational01', 'ConcreteTangentAddition01']" + text[end:]
needle = "originals += [p for e in next_passed for p in e['result']['objects']]\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "FINAL = DIAG / 'transfer-concrete-standard-model-20261010-10'\nfinal_events = [json.loads(line) for line in (FINAL / 'events.jsonl').read_text().splitlines()]\nfinal_passed = [e for e in final_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']\nassert len(final_passed) == 4 and final_events[-1]['result']['status'] == 'passed'\noriginals += [p for e in final_passed for p in e['result']['objects']]\n")
text = text.replace("'transfer-concrete-standard-model-20261010-08']:", "'transfer-concrete-standard-model-20261010-08', 'transfer-concrete-standard-model-20261010-10']:")
text = text.replace("records = [pin(Path(__file__)),", "records = [pin(Path(__file__)), pin(DIAG / 'transfer-concrete-standard-model-20261010-10/prepare.py'),")
text = text.replace("Replay four remaining concrete identity/inverse/torsion/exceptional addition modules; retain the two already qualified origin and Edwards addition modules.", "Replay six named maintained secant/tangent addition modules, importing qualified origin/identity/torsion/exceptional objects.")
text = text.replace("plan['source_repairs'] = 'Remove one observed unused simp argument in mk_neg. No statement/premise/axiom change. Predecessor warning rejection remains zero credit; previously passed modules retain their original receipts.'", "plan['source_repairs'] = 'No edits to declaration/proof bodies in these six maintained modules; complete ordered type/axiom audit directives only. Symbolic polynomial certificates are unchanged.'")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Prepared finite six-module secant/tangent recipe.')
