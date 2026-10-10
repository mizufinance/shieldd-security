"""Prepare the next six named modules only from qualified predecessor objects."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-08/prepare.py'
text = prior.read_text()
digest = hashlib.sha256(prior.read_bytes()).hexdigest()
assert digest == '5ff5bc9efa9b2bc13ea16493657c47f07cd27b467fac57d4d39f46b4823402a2'
start = text.index('MODULES = ')
end = text.index('\n\ndef pin', start)
text = text[:start] + "MODULES = ['EdwardsSecantPolynomials01', 'EdwardsSecantRational01', 'ConcreteSecantAddition01',\n           'EdwardsTangentPolynomials01', 'EdwardsTangentRational01', 'ConcreteTangentAddition01']" + text[end:]
needle = "originals += passed[0]['result']['objects']\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "NEXT = DIAG / 'transfer-concrete-standard-model-20261010-08'\nnext_events = [json.loads(line) for line in (NEXT / 'events.jsonl').read_text().splitlines()]\nnext_passed = [e for e in next_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']\nassert len(next_passed) == 6 and next_events[-1]['result']['status'] == 'passed'\noriginals += [p for e in next_passed for p in e['result']['objects']]\n")
text = text.replace("'transfer-concrete-standard-model-20261010-07']:", "'transfer-concrete-standard-model-20261010-07', 'transfer-concrete-standard-model-20261010-08']:")
text = text.replace("Replay six named maintained origin/Edwards/exceptional addition modules.", "Replay six named maintained secant/tangent addition modules.")
text = text.replace("plan['source_repairs'] = 'Origin addition: replace two unnecessary sequence-focus operators with ordinary sequencing. Conclusions, premises and proof tactics are otherwise unchanged. Predecessor warning rejection remains zero credit.'", "plan['source_repairs'] = 'These six maintained handwritten modules are unchanged apart from complete ordered type/axiom audit directives. Previously corrected origin and torsion proofs are qualified imported objects.'")
text = text.replace("records = [pin(Path(__file__)),", "records = [pin(Path(__file__)), pin(DIAG / 'transfer-concrete-standard-model-20261010-08/prepare.py'),")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Predecessor recipe SHA256 ' + digest)
