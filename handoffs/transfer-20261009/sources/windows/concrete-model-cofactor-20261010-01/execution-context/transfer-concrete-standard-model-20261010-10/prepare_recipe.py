"""Fresh successor for one unused simp argument; retain both accepted modules."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-08/prepare.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == '5ff5bc9efa9b2bc13ea16493657c47f07cd27b467fac57d4d39f46b4823402a2'
text = prior.read_text()
start = text.index('MODULES = ')
end = text.index('\n\ndef pin', start)
text = text[:start] + "MODULES = ['ConcretePointAdditionPilot01', 'ConcreteTorsionAddition01',\n           'EdwardsExceptionalClassification01', 'ConcretePoleAddition01']" + text[end:]
needle = "originals += passed[0]['result']['objects']\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "NEXT = DIAG / 'transfer-concrete-standard-model-20261010-08'\nnext_events = [json.loads(line) for line in (NEXT / 'events.jsonl').read_text().splitlines()]\nnext_passed = [e for e in next_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']\nassert len(next_passed) == 2 and next_events[-1]['result']['status'] == 'failed'\noriginals += [p for e in next_passed for p in e['result']['objects']]\n")
needle = "    text = original.read_text()\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "    if module == 'ConcretePointAdditionPilot01':\n        needle = 'simp [WeierstrassCurve.Affine.Point.some.injEq,\\n    WeierstrassCurve.Affine.negY, curve]'\n        assert text.count(needle) == 1\n        text = text.replace(needle, 'simp [WeierstrassCurve.Affine.negY, curve]')\n")
text = text.replace("'transfer-concrete-standard-model-20261010-07']:", "'transfer-concrete-standard-model-20261010-07', 'transfer-concrete-standard-model-20261010-08']:")
text = text.replace("records = [pin(Path(__file__)),", "records = [pin(Path(__file__)), pin(DIAG / 'transfer-concrete-standard-model-20261010-09/prepare_recipe.py'),")
text = text.replace("Replay six named maintained origin/Edwards/exceptional addition modules.", "Replay four remaining concrete identity/inverse/torsion/exceptional addition modules; retain the two already qualified origin and Edwards addition modules.")
text = text.replace("plan['source_repairs'] = 'Origin addition: replace two unnecessary sequence-focus operators with ordinary sequencing. Conclusions, premises and proof tactics are otherwise unchanged. Predecessor warning rejection remains zero credit.'", "plan['source_repairs'] = 'Remove one observed unused simp argument in mk_neg. No statement/premise/axiom change. Predecessor warning rejection remains zero credit; previously passed modules retain their original receipts.'")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Prepared fresh four-module source successor.')
