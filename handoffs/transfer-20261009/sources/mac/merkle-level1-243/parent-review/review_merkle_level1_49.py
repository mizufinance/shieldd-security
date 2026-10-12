"""Second Merkle level exact finite captured-row coverage; no verifier."""
from pathlib import Path
import json,hashlib,re
J=Path(__file__).resolve().parent;W=J.parent;D=J/'merkle-level1-243-review01';P=W/'mac-merkle-level1-243-kernel-result01';entries=json.loads((P/'source-object-receipt01.json').read_text());assert len(entries)==46;sources={}
for e in entries:
 p=Path(e['source']['path']);b=p.read_bytes();assert len(b)==e['source']['bytes']and hashlib.sha256(b).hexdigest()==e['source']['sha256'];sources[e['module']]=b.decode()
graph=json.loads((J/'source-integration-20261011-01/mac-source-closure1813.json').read_text())['custom_sources'];reused=set(sources)&set(graph);assert reused=={'CapturedMerkleGlobalArithmetic184L01B20','CapturedMerkleGlobalArithmetic184L01B21','CapturedMerkleWide223Pilot'}
for name in reused:
 e=next(x for x in entries if x['module']==name);assert e['source']['sha256']==graph[name]['sha256']and e['source']['bytes']==graph[name]['bytes']
wide=sources['CapturedMerkleWide223Pilot'];assert '.drop 352 |>.take 32'in wide and "List.range' 3922 32"in wide
positions=list(range(3890,3954))
for i in [*range(20),24,25,26]:
 n=f'CapturedMerkleGlobalArithmetic184L01B{i:02d}';s=sources[n];start=3570+16*i;count=16 if i<26 else 8;positions.extend(range(start,start+count));assert 'satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770' in s and 'verifier_links rho satisfied' in s
 if i<4:
  assert f'(MerkleGlobalBody181.arithmeticRows 1).drop {16*i} |>.take {count}' in s and f"List.range' {start} {count}" in s and 'theorem checked : productionCheck=true := by decide +kernel' in s
 else:
  assert f'(MerkleGlobalBody181.arithmeticRows 1).drop {16*i} |>.take {count}' in s and 'check_congr' in s and 'parent_equal' in s and 'all_goals rfl' in s
  nums=re.search(r'change position ∈ \[([^]]+)\]',s)[1];assert [int(x)for x in nums.split(',')]==list(range(start,start+count))
  local=sources[f'CapturedMerkleSparse243L01B{i:02d}'];assert f"List.range' {start} {count}" in local and f'originalRows.drop {16*i-52}' in local
  assert 'CompilerWindowRenaming05.swap 25064 396 1272' in local and 'CompilerWindowRenaming05.swap 23076 396 1988' in local and 'theorem local_checked : localCheck=true := by decide +kernel' in local
  assert [int(x)for x in re.findall(r'^ \| (\d+) => some',local,re.M)]==list(range(start,start+count))
assert len(positions)==len(set(positions))==424 and sorted(positions)==list(range(3570,3994))
s=sources['CapturedMerkleGlobalLevel185L01'];widths=re.search(r'slicesAt \(MerkleGlobalBody181.arithmeticRows 1\) 0 \[([^]]+)\]',s)[1];assert list(map(int,widths.split(',')))==[16]*22+[32,16,16,8]
for t in ['(MerkleGlobalBody181.arithmeticRows 1).length=424','chunks.flatten=MerkleGlobalBody181.arithmeticRows 1','theorem copy_checked : MerkleGlobalBody181.copyCheck 1=true := by decide +kernel','Satisfies rho (MerkleFamily32Whole.rows (F:=F) 1)','MerkleGlobalBody181.sound 1 copy_checked rho satisfied (arithmetic_sound rho satisfied)','CapturedMerkleWide223Pilot.sound rho satisfied']:assert t in s
for i in [*range(20),24,25,26]:assert f'CapturedMerkleGlobalArithmetic184L01B{i:02d}.sound rho satisfied' in s
aud=json.loads((D/'audit-result01.json').read_text());assert aud['declarations']==339 and sum(len(x['audits'])for x in aud['modules']if x['module']not in reused)==315
for n in ['source-generation-review01.json','source-history-review01.json']:assert json.loads((D/n).read_text())['status']=='PASSED'
imp=json.loads((D/'import-guard-review01.json').read_text());assert not(set(imp['custom_associations'])-set(graph)-set(sources))
scope='Exact third Merkle level, family index1: all424 distinct arithmetic positions3570..3993 and actual shared copy200769 derive from the same full captured relation assignment. Exact previously qualified B20/B21 and Wide223Pilot components cover64 positions3890..3953; they are inherited unchanged and not rebuilt. New dense64 plus sparse296 complete the remaining360 positions. Nineteen sparse local16/8 certificates, exact full-provider equality and symbolic transport complete selected satisfaction; exact aggregate428component rows follow from the qualified body theorem while distinct425rows count the shared copy once. No desired selected truth/hash result/local checker result/new assignment caller premise. Forty-three new modules315original reports and three inherited modules24original reports are explicitly separated; unique source graph adds43. Abstract Field/CharP/captured interpretation remains the domain. Complete path/root/hash semantics, concrete field/compiled relation instantiation, Boolean/integer/natural interpretation, lawful seed/all assertion truth, native correspondence/full Transfer remain owned OPEN. Original1588attempt history147failures preserved; guards unchanged; combined replay UNRUN.'
r=dict(status='PASSED',modules=46,reports=339,new_modules=43,new_reports=315,inherited_modules=3,inherited_reports=24,inherited_names=sorted(reused),source_pins=[e['source']for e in entries],arithmetic_positions_half_open=[3570,3994],unique_arithmetic_positions=424,copy_position=200769,unique_selected_rows=425,aggregate_component_rows=428,scope=scope,full_transfer='OPEN',root_verifier_execution='NONE');(D/'source-semantic-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k]for k in ['status','modules','reports','new_modules','new_reports','full_transfer']}))
