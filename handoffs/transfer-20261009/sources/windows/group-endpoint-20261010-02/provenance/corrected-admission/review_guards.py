import copy
import importlib.util
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('bounded_guard_review', ROOT / 'execute_bounded.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
module.PLAN = json.loads((ROOT / 'plan.json').read_text())
floor = json.loads(Path(module.PLAN['external_floor']['path']).read_text())
spend, range_target = module.PLAN['targets'][:2]
module.import_resolution(floor, spend, [])
results = []
def rejected(name, altered_floor, altered_target, expected):
    try: module.import_resolution(altered_floor, altered_target, [])
    except RuntimeError as error:
        assert str(error) == expected, str(error)
        results.append({'case': name, 'result': 'rejected before Lean launch', 'reason': str(error)})
    else: raise AssertionError('Unsafe guard admission: ' + name)
altered = copy.deepcopy(range_target)
altered['imports'] = []
rejected('actual header omission', floor, altered, 'Planned imports differ from actual source header')
altered_floor = dict(floor, modules=dict(floor['modules']))
del altered_floor['modules']['Mathlib.Algebra.Field.Defs']
rejected('direct external root absent from pinned inventory', altered_floor, spend,
    'Direct external import absent from pinned floor: Mathlib.Algebra.Field.Defs')
altered_floor = dict(floor, modules=dict(floor['modules']))
del altered_floor['modules']['Init']
rejected('implicit Init omitted', altered_floor, spend, 'Implicit Init missing from pinned external floor')
receipt = {'valid_spend_import_resolution': 'passed', 'checks': results,
    'lean_processes_launched': 0, 'semantic_negative_control_credit': 0,
    'scope': 'Read-only executor admission checks catch the omitted-root defect; not protocol negative controls.'}
(ROOT / 'guard-review.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt))
