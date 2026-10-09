"""Closed-directory isolated byte replay. Invoke Python with -I -B -S."""
import sys
if not (sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site):
    raise RuntimeError('Required isolated interpreter flags: -I -B -S')
if not __debug__:raise RuntimeError('Optimized Python unsupported')
import argparse,hashlib,json,os,subprocess
from pathlib import Path

a=argparse.ArgumentParser();a.add_argument('--input',type=Path,required=True);a.add_argument('--maintained',type=Path,required=True);a.add_argument('--inventory',type=Path,required=True);a.add_argument('--helpers',type=Path,required=True);a.add_argument('--output-directory',type=Path,required=True);args=a.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inventory_identity=sha(args.inventory)
inv=json.loads(args.inventory.read_bytes());assert inv['schema']=='upstream11-supported-isolated-byte-replay-v2'
assert not Path(__file__).is_symlink() and Path(__file__).resolve()==(args.maintained/'supported_verify_replay.py').resolve(), 'Executing recipe must be the listed file'
assert sha(Path(__file__))==inv['recipe_sha256']==inv['maintained'][Path(__file__).name], 'Executing recipe identity mismatch'
assert sha(args.input)==inv['portable_input_sha256']
assert inv['full_local_descriptor_sha256']=='3be245c6c55f473352481dbbc43d876591f8bbcedb61bd9c9c633de785112d6e'

def closed_flat(directory,expected):
    assert not directory.is_symlink() and directory.is_dir(), 'Directory must be real'
    found={}
    for path in directory.iterdir():
        assert not path.is_symlink() and path.is_file(), 'Directories/symlinks forbidden: '+path.name
        assert path.name in expected and Path(path.name).name==path.name, 'Unlisted entry: '+path.name
        found[path.name]=sha(path)
    assert found==expected, 'Closed flat file set or bytes changed'

closed_flat(args.maintained,inv['maintained']);closed_flat(args.helpers,inv['handwritten_helpers'])
assert all(name in inv['maintained'] and name.endswith('.py') for name in inv['generators'])
out=args.output_directory.resolve();assert not args.output_directory.is_symlink() and not out.exists(), 'Fresh output directory required';out.mkdir(parents=True)
env={name:value for name,value in os.environ.items() if not name.startswith('PYTHON')}
env.update(TRANSFER_UPSTREAM_INPUT=str(args.input.resolve()),TRANSFER_UPSTREAM_PROJECT=str(out/'ShielddSecurity'),TRANSFER_UPSTREAM_OUT=str(out/'metadata'))
# runpy is imported from isolated stdlib BEFORE adding the hash-qualified flat
# directory. -B forbids cache writes; closed-flat rejects any existing cache.
bootstrap='import sys, runpy; sys.path.insert(0, sys.argv[1]); runpy.run_path(sys.argv[2], run_name="__main__")'
observations=[]
for name in inv['generators']:
    closed_flat(args.maintained,inv['maintained']);closed_flat(args.helpers,inv['handwritten_helpers'])
    assert sha(args.input)==inv['portable_input_sha256'] and sha(args.inventory)==inventory_identity
    command=[sys.executable,'-I','-B','-S','-c',bootstrap,str(args.maintained.resolve()),str((args.maintained/name).resolve())]
    try:
        result=subprocess.run(command,env=env,capture_output=True,text=True,timeout=60)
    except subprocess.TimeoutExpired as failure:
        (out/(name+'.stdout')).write_text(failure.stdout or '' if isinstance(failure.stdout,str) else repr(failure.stdout))
        (out/(name+'.stderr')).write_text(failure.stderr or '' if isinstance(failure.stderr,str) else repr(failure.stderr))
        raise
    closed_flat(args.maintained,inv['maintained']);closed_flat(args.helpers,inv['handwritten_helpers'])
    observations.append(dict(generator=name,exit=result.returncode,stdout_sha256=hashlib.sha256(result.stdout.encode()).hexdigest(),stderr_sha256=hashlib.sha256(result.stderr.encode()).hexdigest()))
    if result.returncode:
        (out/(name+'.stdout')).write_text(result.stdout);(out/(name+'.stderr')).write_text(result.stderr)
        (out/'failed-generator.json').write_text(json.dumps(observations[-1],indent=2)+'\n')
        raise RuntimeError('Generator failed: '+name)
closed_flat(args.maintained,inv['maintained']);closed_flat(args.helpers,inv['handwritten_helpers'])
assert sha(args.input)==inv['portable_input_sha256'] and sha(args.inventory)==inventory_identity
observed={p.stem:dict(sha256=sha(p),bytes=p.stat().st_size) for p in (out/'ShielddSecurity').glob('*.lean')}
assert observed==inv['generated'], 'Generated census or source bytes changed'
result=dict(status='passed',generated_sources=len(observed),generated_bytes=sum(x['bytes'] for x in observed.values()),portable_input_sha256=sha(args.input),inventory_sha256=sha(args.inventory),recipe_sha256=sha(Path(__file__)),interpreter=dict(executable=sys.executable,version=sys.version,flags=['-I','-B','-S']),closed_flat_before_after=True,generator_observations=observations,lean_executions=0,full_local_descriptor_sha256=inv['full_local_descriptor_sha256'],scope='Byte identity and closed execution provenance only; no new kernel credit')
(out/'replay-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
