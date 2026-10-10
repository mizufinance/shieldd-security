"""Keep Point02 unqualified; narrowly repair the live temporary-file stat race."""
from pathlib import Path
import json
ROOT = Path(__file__).resolve().parent
DIAG = ROOT.parent
OLD = DIAG / 'transfer-concrete-point-torsion-20261010-02'
NEW = DIAG / 'transfer-concrete-point-torsion-20261010-03'
NEW.mkdir(exist_ok=False)
(NEW / 'handwritten').mkdir()
(NEW / 'handwritten/ConcretePointTorsion01.lean').write_bytes(
    (OLD / 'handwritten/ConcretePointTorsion01.lean').read_bytes())
recipe = (OLD / 'prepare.py').read_text()
before = "body = (PRIOR / 'execute_bounded.py').read_text(); ast.parse(body)"
after = '''body = (PRIOR / 'execute_bounded.py').read_text()
old_usage = """    files = [p for p in ROOT.rglob('*') if p.is_file()]
    total = sum(p.stat().st_size for p in files)
    metadata = sum(p.stat().st_size for p in files if p.suffix in ('.json', '.jsonl', '.txt'))"""
new_usage = """    files = [p for p in ROOT.rglob('*') if p.is_file()]
    sizes = [(p, live_artifact_size(p)) for p in files]
    total = sum(size for _, size in sizes)
    metadata = sum(size for p, size in sizes if p.suffix in ('.json', '.jsonl', '.txt'))"""
assert body.count(old_usage) == 1
body = body.replace(old_usage, new_usage)
old_artifact = "artifact.stat().st_size > OBJECT_CAP"
assert body.count(old_artifact) == 1
body = body.replace(old_artifact, "live_artifact_size(artifact) > OBJECT_CAP")
helper = """def live_artifact_size(path):
    try:
        return path.stat().st_size
    except FileNotFoundError:
        # Lean atomically renames named export temporaries. Accept only a
        # vanished temporary belonging to this plan's target output folder.
        # Every extant temporary/final file is counted again on the next poll,
        # and final output/usage checks run after Lean and its reader exit.
        if (path.parent == ROOT / 'project' / 'ShielddSecurity'
                and '.tmp.' in path.name
                and any(path.name.startswith(t['module'] + '.') for t in PLAN['targets'])):
            return 0
        raise


"""
assert body.count('def usage():') == 1
body = body.replace('def usage():', helper + 'def usage():')
ast.parse(body)'''
assert recipe.count(before) == 1
recipe = recipe.replace(before, after)
before = "plan['retained_failed_history'] = [pin(p) for p in history]"
after = '''second_failed = DIAG / 'transfer-concrete-point-torsion-20261010-02'
second_history = [second_failed / 'plan.json', second_failed / 'events.jsonl',
    second_failed / 'prepare.py', second_failed / 'execute_bounded.py',
    second_failed / 'handwritten/ConcretePointTorsion01.lean',
    second_failed / 'runs/01-ConcretePointTorsion01/stdout.txt']
plan['pins'] += [pin(p) for p in second_history] + [pin(DIAG / 'transfer-concrete-point-race-recipe-20261010-01/prepare.py')]
plan['retained_failed_history'] = [pin(p) for p in history + second_history]'''
assert recipe.count(before) == 1
recipe = recipe.replace(before, after)
before = "plan['repairs'] = 'Fresh successor preserving failed Point01 with zero credit. Convert WithZero to Option before cardinality rewrite; count actual hom kernel membership before converting its predicate to the doubling equation. Same 17 audits, exact import closure, first package composition and finite executor limits.'"
after = "plan['repairs'] = 'Unchanged handwritten Point02 proof. Preserve failed01/02 as zero-credit. Narrow executor fix: tolerate only a disappeared named target .tmp. export during live size sampling; extant/final files remain counted, immutable inputs remain strict, all caps and final audits unchanged.'"
assert recipe.count(before) == 1
recipe = recipe.replace(before, after)
(NEW / 'prepare.py').write_text(recipe, encoding='utf-8', newline='\n')
print(json.dumps({'successor': str(NEW), 'source_changed': False, 'retained_failed_credit': 0}))
