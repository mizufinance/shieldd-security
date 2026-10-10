"""Prepare the complete concrete group model and native cofactor contracts."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-18/prepare.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == '6e0dff0dc900148740e28dd5c68ec1f9ce61d967e550747835c89586d438e0db'
text = prior.read_text()
start = text.index('MODULES = ')
end = text.index('\n\ndef pin', start)
text = text[:start] + "MODULES = ['ConcretePointCoordinates01', 'ConcreteStandardCurveModel01',\n           'GroupNativeAuthorization', 'GroupNativeCofactor']" + text[end:]
text = text.replace("visit('ConcreteStandardCurveModel01')", "visit('ConcreteStandardCurveModel01')\nvisit('GroupNativeCofactor')")
needle = "originals += [p for e in final_passed for p in e['result']['objects']]\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "SECANT = DIAG / 'transfer-concrete-standard-model-20261010-18'\nsecant_events = [json.loads(line) for line in (SECANT / 'events.jsonl').read_text().splitlines()]\nsecant_passed = [e for e in secant_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']\nassert len(secant_passed) == 6 and secant_events[-1]['result']['status'] == 'passed'\noriginals += [p for e in secant_passed for p in e['result']['objects']]\n")
text = text.replace("'transfer-concrete-standard-model-20261010-14']:", "'transfer-concrete-standard-model-20261010-14', 'transfer-concrete-standard-model-20261010-18']:")
text = text.replace("Replay six named secant/tangent modules using all seven qualified origin/addition/torsion/exceptional imports.", "Replay concrete coordinates, complete StandardCurveModel and native authorization/cofactor mathematical contracts using the qualified complete addition proofs. SDK representation and full Transfer correspondence remain open.")
text = text.replace("plan['source_repairs'] = 'Retained SymPy generators reproduce both canonical certificates exactly before atomically regenerating the two whole certificate modules with definitionally unused lets removed. Proposed coefficients/proof identities remain unchanged. Four handwritten secant/tangent transport modules remain unchanged.'", "plan['source_repairs'] = 'These four maintained declaration/proof bodies are unchanged; complete ordered type/axiom audits are appended. Retain regenerated polynomial predecessors with their original qualified receipts.'")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Predecessor recipe SHA256 ' + hashlib.sha256(prior.read_bytes()).hexdigest())
