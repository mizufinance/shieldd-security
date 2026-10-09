"""Explicit-path supported byte regeneration; no Lean or historical bootstrap."""
import argparse,hashlib,json,os,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('Optimized Python unsupported')
a=argparse.ArgumentParser();a.add_argument('--input',type=Path,required=True);a.add_argument('--maintained',type=Path,required=True);a.add_argument('--inventory',type=Path,required=True);a.add_argument('--helpers',type=Path,required=True);a.add_argument('--output-directory',type=Path,required=True);args=a.parse_args()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
inv=json.loads(args.inventory.read_bytes());assert inv['schema']=='upstream11-supported-byte-replay-v1'
assert sha(args.input)==inv['portable_input_sha256']
assert inv['full_local_descriptor_sha256']=='3be245c6c55f473352481dbbc43d876591f8bbcedb61bd9c9c633de785112d6e'
for name,identity in inv['maintained'].items():assert sha(args.maintained/name)==identity, name
for name,identity in inv['handwritten_helpers'].items():assert sha(args.helpers/name)==identity,name
out=args.output_directory.resolve();assert not out.exists(), 'Fresh output directory required';out.mkdir(parents=True)
env=os.environ.copy();env.update(TRANSFER_UPSTREAM_INPUT=str(args.input.resolve()),TRANSFER_UPSTREAM_PROJECT=str(out/'ShielddSecurity'),TRANSFER_UPSTREAM_OUT=str(out/'metadata'))
for name in inv['generators']:subprocess.run([sys.executable,str((args.maintained/name).resolve())],env=env,check=True,capture_output=True,text=True,timeout=60)
observed={p.stem:dict(sha256=sha(p),bytes=p.stat().st_size) for p in (out/'ShielddSecurity').glob('*.lean')}
assert observed==inv['generated'], 'Generated census or source bytes changed'
result=dict(status='passed',generated_sources=len(observed),generated_bytes=sum(x['bytes'] for x in observed.values()),portable_input_sha256=sha(args.input),inventory_sha256=sha(args.inventory),recipe_sha256=sha(Path(__file__)),lean_executions=0,full_local_descriptor_sha256=inv['full_local_descriptor_sha256'],scope='Byte identity only; no new kernel or runtime correspondence credit')
(out/'replay-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
