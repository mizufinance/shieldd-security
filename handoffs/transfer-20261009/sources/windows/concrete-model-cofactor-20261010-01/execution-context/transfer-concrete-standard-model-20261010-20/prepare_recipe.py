"""Retain the passed secant certificate; repair four redundant handwritten tactics."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-18/prepare.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == '6e0dff0dc900148740e28dd5c68ec1f9ce61d967e550747835c89586d438e0db'
text = prior.read_text()
start = text.index('MODULES = ')
end = text.index('\n\ndef pin', start)
text = text[:start] + "MODULES = ['EdwardsSecantRational01', 'ConcreteSecantAddition01',\n           'EdwardsTangentPolynomials01', 'EdwardsTangentRational01', 'ConcreteTangentAddition01']" + text[end:]
needle = "originals += [p for e in final_passed for p in e['result']['objects']]\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "SECANT = DIAG / 'transfer-concrete-standard-model-20261010-18'\nsecant_events = [json.loads(line) for line in (SECANT / 'events.jsonl').read_text().splitlines()]\nsecant_passed = [e for e in secant_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']\nassert len(secant_passed) == 1 and secant_events[-1]['result']['status'] == 'failed'\noriginals += [p for e in secant_passed for p in e['result']['objects']]\n")
needle = "    text = original.read_text()\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "    if module == 'EdwardsSecantRational01':\n        assert text.count('field_simp [nonzeroD] <;> ring') == 4\n        text = text.replace('field_simp [nonzeroD] <;> ring', 'field_simp [nonzeroD]')\n")
text = text.replace("'transfer-concrete-standard-model-20261010-14']:", "'transfer-concrete-standard-model-20261010-14', 'transfer-concrete-standard-model-20261010-18']:")
text = text.replace("Replay six named secant/tangent modules using all seven qualified origin/addition/torsion/exceptional imports.", "Replay five remaining secant/tangent modules using the newly qualified whole secant certificate and all seven prior addition imports.")
text = text.replace("Four handwritten secant/tangent transport modules remain unchanged.", "Remove four observed unreachable ring tactics from the handwritten Cayley quotient lemmas; their statements and premises remain unchanged. Other handwritten transport proofs remain unchanged.")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Prepared fresh five-module successor.')
