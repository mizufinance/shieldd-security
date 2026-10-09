"""Admission controls for the actual successor runner; zero Lean executions."""
import sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
import hashlib,json,shutil,subprocess
from pathlib import Path
S=Path(__file__).resolve().parent;root=S/'controls04';assert not root.exists();root.mkdir();base=json.loads((S/'replay-inventory04.json').read_bytes());observations=[]
for kind in ['unlisted_json','cache_directory','unlisted_pyc','symlink','wrong_recipe_hash','nonisolated']:
 case=root/kind;shutil.copytree(S/'maintained',case/'maintained');inv=case/'inventory.json';payload=dict(base)
 if kind=='unlisted_json':(case/'maintained/json.py').write_text('raise RuntimeError("untrusted shadow")\n')
 if kind=='cache_directory':(case/'maintained/__pycache__').mkdir()
 if kind=='unlisted_pyc':(case/'maintained/unknown.pyc').write_bytes(b'badcache')
 if kind=='symlink':(case/'maintained/extra.py').symlink_to(case/'maintained/generation_common.py')
 if kind=='wrong_recipe_hash':payload['recipe_sha256']='0'*64
 inv.write_text(json.dumps(payload,indent=2)+'\n');flags=[] if kind=='nonisolated' else ['-I','-B','-S'];command=[sys.executable,*flags,str(case/'maintained/supported_verify_replay.py'),'--input',str(S/'portable-input01.json'),'--maintained',str(case/'maintained'),'--inventory',str(inv),'--helpers',str(S/'helpers'),'--output-directory',str(case/'refused-output')]
 result=subprocess.run(command,capture_output=True,text=True,timeout=10)
 expected={'unlisted_json':'Unlisted entry: json.py','cache_directory':'Directories/symlinks forbidden: __pycache__','unlisted_pyc':'Unlisted entry: unknown.pyc','symlink':'Directories/symlinks forbidden: extra.py','wrong_recipe_hash':'Executing recipe identity mismatch','nonisolated':'Required isolated interpreter flags'}[kind]
 assert result.returncode!=0 and expected in result.stderr,(kind,result.stderr)
 assert not (case/'refused-output').exists()
 (case/'refusal.stdout').write_text(result.stdout);(case/'refusal.stderr').write_text(result.stderr)
 observations.append(dict(control=kind,status='expected_admission_refusal',exit=result.returncode,expected_reason=expected,generated_sources=0,lean_executions=0,stdout_sha256=hashlib.sha256(result.stdout.encode()).hexdigest(),stderr_sha256=hashlib.sha256(result.stderr.encode()).hexdigest()))
(root/'result.json').write_text(json.dumps(dict(status='passed',scope='Six actual pre-execution hygiene refusals; no semantic/kernel credit',controls=observations),indent=2)+'\n');print(json.dumps(dict(status='passed',controls=len(observations))))
