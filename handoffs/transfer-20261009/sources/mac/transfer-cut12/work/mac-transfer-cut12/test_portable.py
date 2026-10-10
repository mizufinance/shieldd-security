"""Finite DATA controls for the production isolated replay recipe."""
import hashlib,json,subprocess,sys,shutil
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-transfer-cut12'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
controls=O/'portable-controls01';assert not controls.exists();controls.mkdir()
observations=[]
for name,expected in [('json_shadow','listing is not closed'),('cache_directory','listing is not closed'),
        ('unlisted_pyc','listing is not closed'),('listed_symlink','non-symlink'),
        ('recipe_hash','maintained input changed'),('executing_path','executing recipe path'),('normal_python','requires -I -B -S')]:
    base=controls/name;shutil.copytree(S/'portable01',base)
    maintained=base/'maintained';recipe=maintained/'supported_verify_replay.py';inventory=base/'replay-inventory01.json'
    if name=='json_shadow':(maintained/'json.py').write_text('raise RuntimeError("must never import shadow")\n')
    if name=='cache_directory':(maintained/'__pycache__').mkdir()
    if name=='unlisted_pyc':(maintained/'unlisted.pyc').write_bytes(b'untrusted')
    if name=='listed_symlink':
        p=maintained/'generate_cut.py';target=base/'generator_target.py';p.rename(target);p.symlink_to(target)
    if name=='recipe_hash':
        inv=json.loads(inventory.read_text());inv['maintained_files']['supported_verify_replay.py']='0'*64;inventory.write_text(json.dumps(inv))
    if name=='executing_path':recipe=S/'portable01/maintained/supported_verify_replay.py'
    flags=['-I','-B','-S'] if name!='normal_python' else ['-B']
    receipt=base/'refusal.json';output=base/'generated'
    command=[sys.executable,*flags,str(recipe),'--inventory',str(inventory),'--maintained',str(maintained),
        '--descriptor',str(base/'cut01.json'),'--output',str(output),'--receipt',str(receipt)]
    child=subprocess.run(command,text=True,capture_output=True,timeout=60)
    (base/'stdout.txt').write_text(child.stdout);(base/'stderr.txt').write_text(child.stderr)
    result=json.loads(receipt.read_text())
    assert child.returncode!=0 and result['status']=='refused' and expected in result['reason'],(name,result)
    assert not output.exists(),'generator ran before intended refusal'
    observations.append(dict(control=name,exit=child.returncode,intended_reason=expected,actual_reason=result['reason'],
        receipt_path=str(receipt.relative_to(R)),receipt_sha256=sha(receipt),command=command,
        generators_executed=0,scope='pre-execution provenance/admission refusal; no semantic inequality claim'))
result=O/'portable-controls-result01.json';result.write_text(json.dumps(dict(status='passed',controls=observations,lean_runs=0),indent=2)+'\n')
print(json.dumps(dict(status='passed',controls=len(observations),result_sha256=sha(result))))
