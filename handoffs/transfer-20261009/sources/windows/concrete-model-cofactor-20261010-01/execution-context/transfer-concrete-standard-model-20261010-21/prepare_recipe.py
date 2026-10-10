"""Prepare the concrete full group model plus native mathematical contracts."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-20/prepare.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == '076a4fa7da752beae05707f8638c48face96ecd8e7a868f03c71f831530df030'
text = prior.read_text()
start = text.index('MODULES = ')
end = text.index('\n\ndef pin', start)
text = text[:start] + "MODULES = ['ConcretePointCoordinates01', 'ConcreteStandardCurveModel01',\n           'GroupNativeAuthorization', 'GroupNativeCofactor']" + text[end:]
text = text.replace("visit('ConcreteStandardCurveModel01')", "visit('ConcreteStandardCurveModel01')\nvisit('GroupNativeCofactor')")
needle = "originals += [p for e in secant_passed for p in e['result']['objects']]\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "TANGENT = DIAG / 'transfer-concrete-standard-model-20261010-20'\ntangent_events = [json.loads(line) for line in (TANGENT / 'events.jsonl').read_text().splitlines()]\ntangent_passed = [e for e in tangent_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']\nassert len(tangent_passed) == 5 and tangent_events[-1]['result']['status'] == 'passed'\noriginals += [p for e in tangent_passed for p in e['result']['objects']]\n")
text = text.replace("'transfer-concrete-standard-model-20261010-18']:", "'transfer-concrete-standard-model-20261010-18', 'transfer-concrete-standard-model-20261010-20']:")
text = text.replace("Replay five remaining secant/tangent modules using the newly qualified whole secant certificate and all seven prior addition imports.", "Replay concrete coordinates, complete StandardCurveModel and native authorization/cofactor mathematical contracts from qualified complete addition proofs. SDK representation and full Transfer correspondence remain open.")
start = text.index("plan['source_repairs'] = ")
end = text.index("\nplan['guard_delta'] = ", start)
text = text[:start] + "plan['source_repairs'] = 'These four maintained declaration/proof bodies are unchanged; complete ordered type/axiom audits are appended. Regenerated polynomial imports retain their qualified receipts.'" + text[end:]
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Prepared concrete full model/native contract recipe.')
