"""Explicit portable inputs; byte replay only, never Lean or capture replay."""
import argparse,hashlib,json,os,subprocess,sys
from pathlib import Path
if not __debug__:raise RuntimeError('Optimized Python is unsupported')
S=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
parser=argparse.ArgumentParser()
for name in ['descriptor','tail-reference','parameters','expectations','inherited-dir','workspace']:
 parser.add_argument('--'+name,required=True,type=Path)
a=parser.parse_args();expect=json.loads(a.expectations.read_text())
assert not a.workspace.exists(),'Fresh isolated workspace required'
assert h(a.descriptor.read_bytes())==expect['descriptor_sha256']
assert h(a.tail_reference.read_bytes())==expect['tail_reference_sha256']
assert h(a.parameters.read_bytes())==expect['parameter_sha256']
stage=a.workspace/'work/mac-poseidon-width3-call10';out=a.workspace/'outputs/mac-poseidon-width3-call10';project=stage/'project/ShielddSecurity'
project.mkdir(parents=True);out.mkdir(parents=True)
for name,identity in expect['maintained_inputs'].items():
 b=(S/name).read_bytes();assert h(b)==identity,name;(stage/name).write_bytes(b)
(out/'rounds02.json').write_bytes(a.descriptor.read_bytes())
(out/'tail-reference01.json').write_bytes(a.tail_reference.read_bytes())
parameter=a.workspace/'work/runtime-snapshot/crates/crypto/primitives/params/poseidon381.json'
parameter.parent.mkdir(parents=True);parameter.write_bytes(a.parameters.read_bytes())
reference=json.loads(a.tail_reference.read_text())
for name,identity in reference['source_guards'].items():
 b=(a.inherited_dir/(name+'.lean')).read_bytes();assert h(b)==identity,name;(project/(name+'.lean')).write_bytes(b)
before=set(project.glob('*.lean'))
for generator in expect['generator_order']:
 subprocess.run([sys.executable,str(stage/generator)],check=True,stdout=subprocess.DEVNULL)
produced=set(project.glob('*.lean'))-before;assert len(produced)==len(expect['sources'])
sources=[]
for src in sorted(produced):
 e=expect['sources'][src.stem];assert h(src.read_bytes())==e['replay_sha256'],src.name
 sources.append(dict(module=src.stem,sha256=h(src.read_bytes()),bytes=src.stat().st_size,
   accepted_source_sha256=e['accepted_sha256'],attribution_only_successor=e.get('attribution_only_successor',False)))
assert all(h((S/name).read_bytes())==identity for name,identity in expect['maintained_inputs'].items())
result=dict(status='passed',scope='Portable byte replay,19 generated sources; no Lean replay. AbsorbProof header corrected via maintained template, preserved original accepted source/import closure.',
 recipe_sha256=h(Path(__file__).read_bytes()),expectations_sha256=h(a.expectations.read_bytes()),
 descriptor_sha256=h(a.descriptor.read_bytes()),tail_reference_sha256=h(a.tail_reference.read_bytes()),
 parameter_sha256=h(a.parameters.read_bytes()),maintained_inputs=expect['maintained_inputs'],sources=sources)
dest=out/'replay-result01.json';dest.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='passed',sources=len(sources),result=str(dest))))
