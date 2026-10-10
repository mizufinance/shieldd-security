"""Prepare concrete coordinates/model and the two native group contracts."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-14/prepare.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == '28f56a21cda16320eb6b600d3b1baf46244f24d7d0ed16e9b653a7f349e44b7f'
text = prior.read_text()
start = text.index('MODULES = ')
end = text.index('\n\ndef pin', start)
text = text[:start] + "MODULES = ['ConcretePointCoordinates01', 'ConcreteStandardCurveModel01',\n           'GroupNativeAuthorization', 'GroupNativeCofactor']" + text[end:]
text = text.replace("visit('ConcreteStandardCurveModel01')", "visit('ConcreteStandardCurveModel01')\nvisit('GroupNativeCofactor')")
needle = "originals += [p for e in final_passed for p in e['result']['objects']]\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "SECANT = DIAG / 'transfer-concrete-standard-model-20261010-14'\nsecant_events = [json.loads(line) for line in (SECANT / 'events.jsonl').read_text().splitlines()]\nsecant_passed = [e for e in secant_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']\nassert len(secant_passed) == 6 and secant_events[-1]['result']['status'] == 'passed'\noriginals += [p for e in secant_passed for p in e['result']['objects']]\n")
text = text.replace("'transfer-concrete-standard-model-20261010-13']:", "'transfer-concrete-standard-model-20261010-13', 'transfer-concrete-standard-model-20261010-14']:")
text = text.replace("records = [pin(Path(__file__)),", "records = [pin(Path(__file__)), pin(DIAG / 'transfer-concrete-standard-model-20261010-14/prepare.py'),")
text = text.replace("Replay six named secant/tangent modules using all seven qualified origin/addition/torsion/exceptional imports.", "Replay concrete coordinates and complete StandardCurveModel, then the two native authorization/cofactor mathematical contract modules. All concrete addition proofs are qualified imports. SDK representation correspondence and full Transfer remain open.")
text = text.replace("plan['source_repairs'] = 'These six maintained declaration/proof bodies, including symbolic polynomial certificates, are unchanged. Append complete type/axiom report directives only; no generated proof is edited.'", "plan['source_repairs'] = 'These four maintained declaration/proof bodies are unchanged. Append complete ordered type/axiom report directives only.'")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Prepared concrete full group model/native contract recipe.')
