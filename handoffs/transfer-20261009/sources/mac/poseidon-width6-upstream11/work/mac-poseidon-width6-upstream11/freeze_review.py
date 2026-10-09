"""Immutable read-only source snapshot; does not grant proof acceptance."""
import argparse,hashlib,json,re,shutil
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];P=S/'project';O=R/'outputs/mac-poseidon-width6-upstream11'
a=argparse.ArgumentParser();a.add_argument('--destination',required=True);args=a.parse_args();dest=Path(args.destination).resolve();assert not dest.exists();dest.mkdir(parents=True)
roots=['TransferPoseidonUpstream11Proof01','TransferPoseidonUpstream11Checked01','TransferPoseidonUpstream11Controls01'];pending=roots[:];files=[];seen=set()
def copy(source,path,role):
 raw=source.read_bytes();target=dest/path;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw);files.append(dict(path=path,source_path=str(source.relative_to(R)),sha256=hashlib.sha256(raw).hexdigest(),bytes=len(raw),role=role))
while pending:
 n=pending.pop()
 if n in seen:continue
 seen.add(n);source=P/'ShielddSecurity'/f'{n}.lean';copy(source,f'project/ShielddSecurity/{n}.lean','new_owned' if n.startswith('TransferPoseidonUpstream11') or n in ['CompilerSegmentCompletion11','PoseidonTwoBlockComposition11'] else 'inherited_owned')
 pending+=re.findall(r'^import ShielddSecurity\.(\S+)',source.read_text(),re.M)
for source in sorted(list(S.glob('*.py'))+list(S.glob('*.lean.txt'))):copy(source,'maintained/'+source.name,'maintained')
for name in ['input-packet02.json','import-extension01.json','qualification-result01.json','selection-guard02.json','probe-cost-plan01.json','portable-input01.json']:
 copy(O/name,'inputs/'+name,'identity_or_data_only')
for name in ['lakefile.lean','lake-manifest.json','lean-toolchain']:copy(P/name,'project/'+name,'package_identity')
m=dict(schema='upstream11-source-only-review-v2',published_ACK='9489b759610e5026b9e5b8cb55ff40022b4e72c8',roots=roots,files=files,source_only=True,proof_acceptance=False,classification='Fresh only actual upstream11 commands; copied Call10/earlier receipts are inherited, zero fresh executions.',portable_recipe='OPEN; input candidate included, recipe requires separate review delta',scope='Cut-LC mathematical same-rho 2-block hash6 and child hash3; selected1153rows. Native/global/later-consumer/upstream-cut semantics OPEN.')
raw=(json.dumps(m,indent=2)+'\n').encode();(dest/'manifest.json').write_bytes(raw);print(json.dumps(dict(manifest=str(dest/'manifest.json'),sha256=hashlib.sha256(raw).hexdigest(),files=len(files),lean_closure=len(seen))))
