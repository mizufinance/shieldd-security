"""Correct observed unused torsion premises/tactics in a fresh successor."""
import ast
import hashlib
from pathlib import Path
ROOT = Path(__file__).resolve().parent
prior = ROOT.parent / 'transfer-concrete-standard-model-20261010-10/prepare.py'
assert hashlib.sha256(prior.read_bytes()).hexdigest() == '67d3b7b1e7a4c571b752522f8659b9123556b01df4f0618492c5941a9d733853'
text = prior.read_text()
start = text.index('MODULES = ')
end = text.index('\n\ndef pin', start)
text = text[:start] + "MODULES = ['ConcreteTorsionAddition01', 'EdwardsExceptionalClassification01', 'ConcretePoleAddition01']" + text[end:]
needle = "originals += [p for e in next_passed for p in e['result']['objects']]\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "LAST = DIAG / 'transfer-concrete-standard-model-20261010-10'\nlast_events = [json.loads(line) for line in (LAST / 'events.jsonl').read_text().splitlines()]\nlast_passed = [e for e in last_events if e['event'] == 'attempt_finished' and e['result']['status'] == 'passed']\nassert len(last_passed) == 1 and last_events[-1]['result']['status'] == 'failed'\noriginals += [p for e in last_passed for p in e['result']['objects']]\n")
needle = "    text = original.read_text()\n"
assert text.count(needle) == 1
text = text.replace(needle, needle + "    if module == 'ConcreteTorsionAddition01':\n        assert text.count('variable [DecidableEq F]\\n\\n') == 1\n        text = text.replace('variable [DecidableEq F]\\n\\n', '')\n        text = text.replace('theorem regular_equivalence ', 'variable [DecidableEq F]\\n\\ntheorem regular_equivalence ')\n        needle = 'simp only [WeierstrassCurve.Affine.Point.some.injEq, xValue, yValue, and_self]'\n        assert text.count(needle) == 1\n        text = text.replace(needle, 'simp only [xValue, yValue]')\n")
text = text.replace("'transfer-concrete-standard-model-20261010-08']:", "'transfer-concrete-standard-model-20261010-08', 'transfer-concrete-standard-model-20261010-10']:")
text = text.replace("records = [pin(Path(__file__)),", "records = [pin(Path(__file__)), pin(DIAG / 'transfer-concrete-standard-model-20261010-11/prepare_recipe.py'),")
text = text.replace("Replay four remaining concrete identity/inverse/torsion/exceptional addition modules; retain the two already qualified origin and Edwards addition modules.", "Replay three remaining torsion and exceptional addition modules; retain three already qualified addition modules.")
text = text.replace("plan['source_repairs'] = 'Remove one observed unused simp argument in mk_neg. No statement/premise/axiom change. Predecessor warning rejection remains zero credit; previously passed modules retain their original receipts.'", "plan['source_repairs'] = 'Move DecidableEq section scope after regular_minus/regular_plus, removing their unused typeclass premise; remove two observed unused simp arguments. No conclusion change or new axiom. Prior rejected torsion attempt remains zero credit.'")
ast.parse(text)
(ROOT / 'prepare.py').write_text(text, encoding='utf-8', newline='\n')
print('Prepared fresh torsion/exceptional successor.')
