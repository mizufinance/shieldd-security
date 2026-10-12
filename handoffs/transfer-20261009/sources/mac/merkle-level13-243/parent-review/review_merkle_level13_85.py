"""Ninth Merkle family exact coverage; no verifier."""
from pathlib import Path
import json,hashlib,re
J=Path(__file__).resolve().parent;W=J.parent;D=J/'merkle-level13-243-review01';P=W/'mac-merkle-level13-243-kernel-result01';entries=json.loads((P/'source-object-receipt01.json').read_text());assert len(entries)==51;sources={}
for e in entries:
 p=Path(e['source']['path']);b=p.read_bytes();assert len(b)==e['source']['bytes']and hashlib.sha256(b).hexdigest()==e['source']['sha256'];sources[e['module']]=b.decode()
graph=json.loads((J/'source-integration-20261011-01/mac-source-closure2417.json').read_text())['custom_sources'];assert not(set(sources)&set(graph))
positions=[]
for i in range(27):
 n=f'CapturedMerkleGlobalArithmetic184L13B{i:02d}';s=sources[n];start=8658+16*i;count=16 if i<26 else 8;positions.extend(range(start,start+count));assert 'satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770'in s and 'verifier_links rho satisfied'in s
 assert f'(MerkleGlobalBody181.arithmeticRows 13).drop {16*i} |>.take {count}'in s
 if i<4:assert f"List.range' {start} {count}"in s and 'theorem checked : productionCheck=true := by decide +kernel'in s
 else:
  assert 'check_congr'in s and 'parent_equal'in s and 'all_goals rfl'in s
  nums=re.search(r'change position ∈ \[([^]]+)\]',s)[1];assert [int(x)for x in nums.split(',')]==list(range(start,start+count))
  local=sources[f'CapturedMerkleSparse243L13B{i:02d}'];assert f"List.range' {start} {count}"in local and f'originalRows.drop {16*i-52}'in local
  assert 'CompilerWindowRenaming05.swap 25064 396 6360'in local and 'CompilerWindowRenaming05.swap 23076 396 1988'in local and 'theorem local_checked : localCheck=true := by decide +kernel'in local
  assert [int(x)for x in re.findall(r'^ \| (\d+) => some',local,re.M)]==list(range(start,start+count))
assert len(positions)==len(set(positions))==424 and sorted(positions)==list(range(8658,9082))
s=sources['CapturedMerkleGlobalLevel185L13'];widths=re.search(r'slicesAt \(MerkleGlobalBody181.arithmeticRows 13\) 0 \[([^]]+)\]',s)[1];assert list(map(int,widths.split(',')))==[16]*26+[8]
for t in ['(MerkleGlobalBody181.arithmeticRows 13).length=424','chunks.flatten=MerkleGlobalBody181.arithmeticRows 13','theorem copy_checked : MerkleGlobalBody181.copyCheck 13=true := by decide +kernel','Satisfies rho (MerkleFamily32Whole.rows (F:=F) 13)','MerkleGlobalBody181.sound 13 copy_checked rho satisfied (arithmetic_sound rho satisfied)']:assert t in s
for i in range(27):assert f'CapturedMerkleGlobalArithmetic184L13B{i:02d}.sound rho satisfied'in s
aud=json.loads((D/'audit-result01.json').read_text());assert aud['declarations']==375 and len(aud['modules'])==51
for n in ['source-generation-review01.json','source-history-review01.json']:assert json.loads((D/n).read_text())['status']=='PASSED'
imp=json.loads((D/'import-guard-review01.json').read_text());assert not(set(imp['custom_associations'])-set(graph)-set(sources))
history=json.loads((D/'source-history-review01.json').read_text());assert history['attempts']==2201 and history['failed']==147
scope='Exact fifteenth Merkle level, family index13: all424 distinct arithmetic positions8658..9081 and shared actual copy200769 derive from the same full captured relation assignment. New dense64 and twenty-three sparse local16/8 certificates cover all424; exact full-provider equality and symbolic transport yield selected satisfaction. Qualified body theorem derives428 aggregate component rows with shared copy counted once among425 distinct rows. No caller desired selected truth/hash result/local-checker result/new assignment premise. Fifty-one new modules375 original complete reports, no newly selected inherited modules; unique graph adds51. Abstract Field/CharP/captured interpretation remains the domain. Complete path/root/hash semantics, concrete field/compiled relation instantiation, Boolean/integer/natural interpretation, lawful seed/all assertion truth, native correspondence/full Transfer remain owned OPEN. Original2201attempt history147failures preserved. Guard272 historical audit memo independently reviewed28 under unchanged physical limits; combined replay UNRUN.'
r=dict(status='PASSED',modules=51,reports=375,new_modules=51,new_reports=375,inherited_modules=0,inherited_reports=0,inherited_names=[],source_pins=[e['source']for e in entries],arithmetic_positions_half_open=[8658,9082],unique_arithmetic_positions=424,copy_position=200769,unique_selected_rows=425,aggregate_component_rows=428,scope=scope,full_transfer='OPEN',root_verifier_execution='NONE');(D/'source-semantic-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k]for k in ['status','modules','reports','new_modules','new_reports','full_transfer']}))

