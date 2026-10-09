"""Isolated source byte replay from the shipped compact exact consumer input."""
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('Optimized Python is unsupported')
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-width3-rename09';h=lambda b:hashlib.sha256(b).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--input',required=True,type=Path);p.add_argument('--output',required=True,type=Path);a=p.parse_args();assert h(a.input.read_bytes())=='dc2d6805fbd8a344d30101092d8d266c39c49e9fdf069adcb3933d1f3c213fac';assert not a.output.exists();stage=a.output/'work/mac-poseidon-width3-rename09';stage.mkdir(parents=True);out=a.output/'outputs/mac-poseidon-width3-rename09';out.mkdir(parents=True);(stage/'project/ShielddSecurity').mkdir(parents=True)
gens=['generate_leaf.py','generate_tail_program.py','generate_tail_semantic.py','generate_second_data.py','generate_row_checks.py','generate_port_checks.py','generate_second_proof.py','generate_page.py','generate_page_endpoint.py','generate_controls.py'];inputs=gens+['generation_common.py','tail-semantic-template.lean.txt','ports-template.lean.txt','second-proof-template.lean.txt'];identities={}
for n in inputs:
 b=(S/n).read_bytes();identities[n]=h(b);(stage/n).write_bytes(b)
env=dict(os.environ,RENAME09_REPLAY_INPUT=str(a.input.resolve()))
for g in gens:subprocess.run([sys.executable,str(stage/g)],env=env,check=True,stdout=subprocess.DEVNULL)
files=[]
for src in sorted((stage/'project/ShielddSecurity').glob('*.lean')):
 expected=S/'project/ShielddSecurity'/src.name;assert src.read_bytes()==expected.read_bytes(),src.name
 files.append(dict(module=src.stem,sha256=h(src.read_bytes()),bytes=src.stat().st_size))
assert len(files)==46,len(files)
assert all(h((S/n).read_bytes())==v for n,v in identities.items())
result=dict(status='passed',verification='Byte-identical generated source replay; no Lean replay',recipe_sha256=h(Path(__file__).read_bytes()),input_sha256=h(a.input.read_bytes()),maintained_inputs=identities,sources=files)
(out/'replay-result01.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status='passed',sources=len(files),result=str(out/'replay-result01.json'))))
