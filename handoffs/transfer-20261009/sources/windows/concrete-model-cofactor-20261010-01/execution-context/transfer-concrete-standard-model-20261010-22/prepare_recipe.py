"""Fresh model scope correction; keep the qualified coordinate representation."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-21/prepare.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == '0ea843e12fdd0ccb521f9c404be1fa042475f522f73c95a95b2af9fc98f68d92'
text = prior.read_text()
text = text.replace("MODULES = ['ConcretePointCoordinates01', 'ConcreteStandardCurveModel01',", "MODULES = ['ConcreteStandardCurveModel01',")
needle = "originals += [p for e in tangent_passed for p in e['result']['objects']]\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "COORD = DIAG / 'transfer-concrete-standard-model-20261010-21'\ncoordinate_events = [json.loads(line) for line in (COORD / 'events.jsonl').read_text().splitlines()]\ncoordinate_passed = [e for e in coordinate_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']\nassert len(coordinate_passed) == 1 and coordinate_events[-1]['result']['status'] == 'failed'\noriginals += [p for e in coordinate_passed for p in e['result']['objects']]\n")
needle = "    text = original.read_text()\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "    if module == 'ConcreteStandardCurveModel01':\n        assert text.count('variable [DecidableEq F]\\n\\n') == 1\n        text = text.replace('variable [DecidableEq F]\\n\\n', '')\n        marker = '/-- Addition compatibility for all Edwards points'\n        assert text.count(marker) == 1\n        text = text.replace(marker, 'variable [DecidableEq F]\\n\\n' + marker)\n")
text = text.replace("'transfer-concrete-standard-model-20261010-20']:", "'transfer-concrete-standard-model-20261010-20', 'transfer-concrete-standard-model-20261010-21']:")
text = text.replace("Replay concrete coordinates, complete StandardCurveModel and native authorization/cofactor mathematical contracts from qualified complete addition proofs.", "Replay complete StandardCurveModel and native authorization/cofactor mathematical contracts from qualified concrete coordinate/addition proofs.")
text = text.replace("These four maintained declaration/proof bodies are unchanged; complete ordered type/axiom audits are appended.", "Model zero_x_classification loses its observed unused DecidableEq premise by narrowing section scope; all conclusions are unchanged. Native contract declaration/proof bodies are unchanged. Complete ordered type/axiom audits are appended.")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Predecessor recipe SHA256 ' + hashlib.sha256(prior.read_bytes()).hexdigest())
