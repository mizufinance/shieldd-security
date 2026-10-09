"""Portable byte replay; no capture qualification or kernel replay is claimed."""
import argparse,hashlib,json,shutil,subprocess,sys,time
from pathlib import Path
parser=argparse.ArgumentParser()
for name in ['manifest','envelope','source-dir','small-descriptor','descriptor','parameter','output']:parser.add_argument('--'+name,type=Path,required=True)
a=parser.parse_args();assert __debug__,'optimization disables validation'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();started=time.monotonic()
manifest=json.loads(a.manifest.read_text());envelope=json.loads(a.envelope.read_text());assert sha(a.manifest)==envelope['producer_manifest_sha256']
assert manifest['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
assert sha(a.small_descriptor)=='fde97d467a132f7a53d037515cd35fbdcdf24c7f393b3195d1aa38885ca7f575'
assert sha(a.descriptor)=='6d903d9380ab2e54b6e0207b5283c3786ea33a1500b7124a1d944bd3da452975'
assert sha(a.parameter)=='f45040142a56e16bb8480f1f6648621d32f456646cfaf77beca2b05a6bb12742'
generators=['generate_direct.py','generate_absorption.py','generate_absorption_controls.py','generate_full_blocks.py','generate_full_block_proofs.py','generate_full_block_certificates.py','generate_full_program.py','generate_full_semantic.py','generate_full_checked.py']
templates=['direct-proof-template.lean.txt','absorption-proof-template.lean.txt','full-round-proof-template.lean.txt','full-semantic-template.lean.txt','full-checked-template.lean.txt','full-controls-template.lean.txt']
inputs=generators+templates+['validate_records.py','export_rounds.py','parent-descriptor.json']
entries={Path(item['path']).name:item for item in manifest['files'] if item['publication'] and (item['path'].startswith('work/mac-poseidon-width3-08/') and '/project/' not in item['path'])}
source_identities=[]
for name in inputs:
 source=a.source_dir/name;assert name in entries and sha(source)==entries[name]['sha256'],name
 source_identities.append(dict(name=name,sha256=sha(source)))
assert not a.output.exists(),'fresh output required'
s=a.output/'work/mac-poseidon-width3-08';o=a.output/'outputs/mac-poseidon-width3-08';p=s/'project/ShielddSecurity';p.mkdir(parents=True);o.mkdir(parents=True)
for name in inputs:shutil.copyfile(a.source_dir/name,s/name)
shutil.copyfile(a.small_descriptor,o/'rounds01.json');shutil.copyfile(a.descriptor,o/'rounds-full01.json')
parameter=a.output/'work/runtime-snapshot/crates/crypto/primitives/params/poseidon381.json';parameter.parent.mkdir(parents=True);shutil.copyfile(a.parameter,parameter)
commands=[]
for name in generators:
 cmd=[sys.executable,str((s/name).resolve())];subprocess.run(cmd,cwd=a.output,check=True,stdout=subprocess.DEVNULL);commands.append(cmd)
# Three template-produced small Proof01 files lack GENERATED headers; source
# production, rather than that header heuristic, determines their classification.
expected={Path(item['path']).name:item for item in manifest['files'] if item['category']=='generated_instance' or (Path(item['path']).name.startswith('TransferPoseidonWidth3R') and Path(item['path']).name.endswith('Proof01.lean'))}
assert len(expected)==78 and {q.name for q in p.glob('*.lean')}==set(expected)
for name,item in expected.items():assert sha(p/name)==item['sha256'],name
assert all(sha(a.source_dir/item['name'])==item['sha256'] for item in source_identities)
result=dict(schema='portable-width3-supported-replay-v1',status='passed',producer_manifest_sha256=sha(a.manifest),envelope_sha256=sha(a.envelope),source_inputs=source_identities,parameter_sha256=sha(a.parameter),small_descriptor_sha256=sha(a.small_descriptor),descriptor_sha256=sha(a.descriptor),commands=commands,generated_sources=78,all_bytes_equal_sealed=True,bootstrap=dict(sha256='6ced33549fe38fc74cb8559ea02c01ebcb41af5d0c31d14997f9b1a23dce3b89',classification='historical source-only bootstrap, unsupported; never read or invoked'),kernel_runs=0,proof_credit_change=0,scope='byte regeneration from exact supplied finite descriptors; raw capture/native/kernel requalification not performed',seconds=time.monotonic()-started)
(a.output/'replay-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status='passed',sources=78,seconds=result['seconds'])),flush=True)
