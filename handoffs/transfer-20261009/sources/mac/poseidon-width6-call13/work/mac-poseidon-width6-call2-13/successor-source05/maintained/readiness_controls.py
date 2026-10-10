"""Source/portable guard controls only. No Lean or other heavy subprocess."""
import argparse,hashlib,json,shutil,sys,tempfile
from pathlib import Path
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
S=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('--inventory',type=Path,required=True);parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();inventory=json.loads(args.inventory.read_text())
assert {p.name for p in S.iterdir()}==set(inventory['maintained_files'])
for name,e in inventory['maintained_files'].items():
    p=S/name
    assert p.is_file() and not p.is_symlink() and hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256'] and p.stat().st_size==e['bytes']
assert hashlib.sha256(Path(__file__).read_bytes()).hexdigest()==inventory['maintained_files'][Path(__file__).name]['sha256']
sys.path.insert(0,str(S))
from source_contract import closed,safe_lean
closed(S,inventory,Path(__file__))
positive='-- sorry native_decide unsafe\n/- nested /- unsafe -/ comments -/\ntheorem valid : True := by decide +kernel\n'
safe_lean(positive)
tokens=['sorry','admit','axiom','native_decide','decide +native','decide +kernel +native',
        'Lean.ofReduceBool','debug.skipKernelTC','unsafe','implemented_by','extern']
refusals=[]
for token in tokens:
    try:safe_lean('def example := '+token)
    except AssertionError:refusals.append(token)
    else:raise AssertionError('unsafe token accepted: '+token)
directory_refusals=[]
with tempfile.TemporaryDirectory(prefix='call13-closed-controls-') as temp:
    root=Path(temp)
    for mode in ['unlisted_json','pyc','directory','symlink']:
        copy=root/mode;shutil.copytree(S,copy)
        if mode=='unlisted_json':(copy/'json.py').write_text('raise RuntimeError("shadow")\n')
        elif mode=='pyc':(copy/'unlisted.pyc').write_bytes(b'bad')
        elif mode=='directory':(copy/'__pycache__').mkdir()
        else:
            (copy/'audit_log.py').unlink()
            (copy/'audit_log.py').symlink_to(S/'audit_log.py')
        try:closed(copy,inventory,copy/Path(__file__).name)
        except AssertionError:directory_refusals.append(mode)
        else:raise AssertionError('directory control accepted: '+mode)
closed(S,inventory,Path(__file__))
result={'status':'passed','positive_comment_kernel_token_case':True,'forbidden_Lean_token_refusals':refusals,
        'closed_directory_refusals':directory_refusals,'kernel_runs':0,'scope':'Python source/preexecution hygiene guard tests only, NOT Lean semantic controls',
        'recipe_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
with args.output.open('x') as handle:json.dump(result,handle,indent=2);handle.write('\n')
print(json.dumps({'status':'passed','token_refusals':len(refusals),'directory_refusals':len(directory_refusals),'kernel_runs':0}))
