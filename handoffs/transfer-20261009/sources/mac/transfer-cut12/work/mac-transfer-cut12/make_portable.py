"""Freeze the final maintained replay directory and accepted byte identities."""
import hashlib,json,shutil
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-transfer-cut12';P=S/'portable01'
assert not P.exists();P.mkdir();M=P/'maintained';M.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
names=['generate_probe.py','generate_cut.py','generate_join.py','generate_checked.py','supported_verify_replay.py']
maintained={}
for name in names:
 shutil.copyfile(S/name,M/name);maintained[name]=sha(M/name)
generated={}
for name,index in [('TransferCut12ProbeData01',1),('TransferCut12ProductProbe01',1),('TransferCut12Data01',2),('TransferCut12Proof01',1),('TransferCut12Joined01',2),('TransferCut12Checked01',1),('TransferCut12Controls01',2)]:
 source=S/'project/ShielddSecurity'/f'{name}.lean';r=json.loads((O/f'build-{name}-{index:02d}.json').read_text())
 assert r['status']=='passed' and sha(source)==r['source_sha256']
 generated[source.name]=dict(sha256=sha(source),bytes=source.stat().st_size)
shutil.copyfile(O/'cut01.json',P/'cut01.json')
inventory=dict(schema='closed-isolated-cut12-replay-v1',maintained_files=maintained,
 generator_order=names[:-1],generated_sources=generated,descriptor_sha256=sha(P/'cut01.json'),
 runtime_sha='844389ee069e1fb2e576708842d0b389b4d9a44a',scope='Seven accepted generated sources; zero Lean replay')
p=P/'replay-inventory01.json';p.write_text(json.dumps(inventory,indent=2)+'\n')
print(json.dumps(dict(inventory_sha256=sha(p),recipe_sha256=maintained['supported_verify_replay.py'],generated=len(generated),directory=str(P))))
