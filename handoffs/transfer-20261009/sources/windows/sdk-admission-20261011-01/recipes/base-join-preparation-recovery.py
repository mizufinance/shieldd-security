"""Restore the unrun01 prepared source and stage later annotations only in fresh02."""
import ast
import hashlib
import json
from pathlib import Path
import shutil
ROOT = Path(__file__).resolve().parent
OLD = ROOT.parent / 'transfer-sdk-spend-auth-join-20261010-01'
handwritten = OLD / 'handwritten/SDKSpendAuthSubgroup01.lean'
prepared = OLD / 'project/ShielddSecurity/SDKSpendAuthSubgroup01.lean'
assert not (OLD / 'events.jsonl').exists()
assert hashlib.sha256(handwritten.read_bytes()).hexdigest() == '63f1ff1f52ad0053a2ce704d333a42c42bb883ed12a9a4ec6531be9218c70a6d'
assert hashlib.sha256(prepared.read_bytes()).hexdigest() == '1efed17d3d9c9677930e66d5d7a68d357d3e810e4b82b0c08d4bbc646acc2b16'
body = handwritten.read_text().split('\nset_option pp.all true in\n#check')[0]
(ROOT / 'handwritten').mkdir(exist_ok=False)
(ROOT / 'handwritten/SDKSpendAuthSubgroup01.lean').write_text(body,encoding='utf-8',newline='\n')
shutil.copyfile(prepared,handwritten)
assert hashlib.sha256(handwritten.read_bytes()).hexdigest() == '1efed17d3d9c9677930e66d5d7a68d357d3e810e4b82b0c08d4bbc646acc2b16'
receipt = {'kind':'OWN_UNRUN_PREPARATION_RACE_RECOVERY','superseded_plan':str(OLD/'plan.json'),
    'prepared_source_sha256':'1efed17d3d9c9677930e66d5d7a68d357d3e810e4b82b0c08d4bbc646acc2b16',
    'restored_prepared_pin':True,'annotations_staged_only_in_fresh02':True,'unrun01':True,
    'proof_credit':0,'semantic_negative_control_credit':0}
(ROOT / 'preparation-recovery.json').write_text(json.dumps(receipt,indent=2)+'\n')
recipe = (OLD / 'prepare_recipe.py').read_text()
recipe = recipe.replace('ast.parse(text)', 'text = text.replace("pin(ROOT / \'prepare_recipe.py\'), pin(source)", "pin(ROOT / \'prepare_recipe.py\'), pin(ROOT / \'prepare_fresh.py\'), pin(ROOT / \'preparation-recovery.json\'), pin(source)")\nast.parse(text)')
ast.parse(recipe)
(ROOT / 'prepare_recipe.py').write_text(recipe,encoding='utf-8',newline='\n')
print('Unrun01 original prepared source restored byte-exact; added annotations staged only in fresh02.')
