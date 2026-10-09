"""Exercise meaningful closed-directory refusals using disposable pinned copies."""
import json,hashlib,shutil,subprocess,sys
from pathlib import Path
H=Path(__file__).resolve().parent;F=H/'frozen';D=H/'data-controls01';assert not D.exists();D.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
results=[]
for case in ['unlisted_module','cache_directory','unlisted_pyc','symlink','wrong_recipe_hash','nonisolated']:
    c=D/case;c.mkdir();m=c/'maintained';shutil.copytree(F/'maintained',m);helpers=c/'helpers';shutil.copytree(F/'helpers',helpers)
    inventory=c/'inventory.json';shutil.copyfile(F/'replay-inventory04.json',inventory)
    if case=='unlisted_module':(m/'json.py').write_text('UNLISTED_SENTINEL = 1\n')
    elif case=='cache_directory':(m/'__pycache__').mkdir()
    elif case=='unlisted_pyc':(m/'unlisted.pyc').write_bytes(b'guard-control')
    elif case=='symlink':
        p=m/'generate_prefix.py';p.unlink();p.symlink_to(F/'maintained/generate_prefix.py')
    elif case=='wrong_recipe_hash':
        j=json.loads(inventory.read_text());j['recipe_sha256']='0'*64;inventory.write_text(json.dumps(j)+'\n')
    flags=[] if case=='nonisolated' else ['-I','-B','-S']
    out=c/'generated'
    command=[sys.executable,*flags,str(m/'supported_verify_replay.py'),'--input',str(F/'portable-input01.json'),'--maintained',str(m),'--inventory',str(inventory),'--helpers',str(helpers),'--output-directory',str(out)]
    r=subprocess.run(command,capture_output=True,text=True,timeout=30)
    assert r.returncode!=0 and not out.exists(),case
    expected='Executing recipe identity mismatch' if case=='wrong_recipe_hash' else 'Required isolated interpreter flags' if case=='nonisolated' else 'Directories/symlinks forbidden' if case in ['cache_directory','symlink'] else 'Unlisted entry'
    assert expected in r.stderr,(case,r.stderr)
    results.append({'case':case,'exit':r.returncode,'expected_refusal':expected,'stderr_sha256':hashlib.sha256(r.stderr.encode()).hexdigest(),'output_created':out.exists(),'Lean_executions':0})
inventory=json.loads((F/'replay-inventory04.json').read_text());assert {p.name:sha(p) for p in (F/'maintained').iterdir()}==inventory['maintained']
assert not list(F.rglob('*.pyc')) and not list(F.rglob('__pycache__'))
result={'schema':'parent-isolated-replay-closed-directory-data-controls-v1','controls':results,'rejected':len(results),'original_frozen_maintained_directory_exact':True,'no_bytecode_created_in_frozen':True,'kernel_executions':0,'mathematical_results':0,'full_transfer':'OPEN'}
p=H/'data-control-audit01.json';assert not p.exists();p.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
