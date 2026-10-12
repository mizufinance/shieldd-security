"""Second Merkle level exact finite captured-row coverage; no verifier."""
from pathlib import Path
import json,hashlib,re
J=Path(__file__).resolve().parent;W=J.parent;D=J/'merkle-level0-243-review01';P=W/'mac-merkle-level0-243-kernel-result01';entries=json.loads((P/'source-object-receipt01.json').read_text());assert len(entries)==51;sources={}
for e in entries:
 p=Path(e['source']['path']);b=p.read_bytes();assert len(b)==e['source']['bytes']and hashlib.sha256(b).hexdigest()==e['source']['sha256'];sources[e['module']]=b.decode()
graph=json.loads((J/'source-integration-20261011-01/mac-source-closure1763.json').read_text())['custom_sources'];reused=set(sources)&set(graph);assert reused=={'CapturedMerkleGlobalPilot182'}
pilot=next(e for e in entries if e['module']=='CapturedMerkleGlobalPilot182');assert pilot['source']['sha256']==graph['CapturedMerkleGlobalPilot182']['sha256'];s=sources['CapturedMerkleGlobalPilot182'];assert "List.range' 3146 16" in s and '(MerkleGlobalBody181.arithmeticRows 0)' in s and 'satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770' in s
positions=list(range(3146,3162))
for i in range(1,27):
 n=f'CapturedMerkleGlobalArithmetic184L00B{i:02d}';s=sources[n];start=3146+16*i;count=16 if i<26 else 8;positions.extend(range(start,start+count));assert 'satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770' in s and 'verifier_links rho satisfied' in s
 if i<4:
  assert f'(MerkleGlobalBody181.arithmeticRows 0).drop {16*i} |>.take {count}' in s and f"List.range' {start} {count}" in s and 'theorem checked : productionCheck=true := by decide +kernel' in s
 else:
  assert f'(MerkleGlobalBody181.arithmeticRows 0).drop {16*i} |>.take {count}' in s and 'check_congr' in s and 'parent_equal' in s and 'all_goals rfl' in s
  nums=re.search(r'change position ∈ \[([^]]+)\]',s)[1];assert [int(x)for x in nums.split(',')]==list(range(start,start+count))
  local=sources[f'CapturedMerkleSparse243L00B{i:02d}'];assert f"List.range' {start} {count}" in local and f'originalRows.drop {16*i-52}' in local
  assert 'CompilerWindowRenaming05.swap 25064 396 848' in local and 'CompilerWindowRenaming05.swap 23076 396 1988' in local and 'theorem local_checked : localCheck=true := by decide +kernel' in local
  assert [int(x)for x in re.findall(r'^ \| (\d+) => some',local,re.M)]==list(range(start,start+count))
assert positions==list(range(3146,3570))
s=sources['CapturedMerkleGlobalLevel185L00'];widths=re.search(r'slicesAt \(MerkleGlobalBody181.arithmeticRows 0\) 0 \[([^]]+)\]',s)[1];assert list(map(int,widths.split(',')))==[16]*26+[8]
for t in ['(MerkleGlobalBody181.arithmeticRows 0).length=424','chunks.flatten=MerkleGlobalBody181.arithmeticRows 0','theorem copy_checked : MerkleGlobalBody181.copyCheck 0=true := by decide +kernel','Satisfies rho (MerkleFamily32Whole.rows (F:=F) 0)','MerkleGlobalBody181.sound 0 copy_checked rho satisfied (arithmetic_sound rho satisfied)','CapturedMerkleGlobalPilot182.sound rho satisfied']:assert t in s
for i in range(1,27):assert f'CapturedMerkleGlobalArithmetic184L00B{i:02d}.sound rho satisfied' in s
aud=json.loads((D/'audit-result01.json').read_text());assert aud['declarations']==375 and sum(len(x['audits'])for x in aud['modules']if x['module']not in reused)==369
for n in ['source-generation-review01.json','source-history-review01.json']:assert json.loads((D/n).read_text())['status']=='PASSED'
imp=json.loads((D/'import-guard-review01.json').read_text());assert not(set(imp['custom_associations'])-set(graph)-set(sources))
scope='Exact second Merkle level, family index0: all424 distinct arithmetic positions3146..3569 and the actual shared copy200769 derive from the same full captured relation assignment. Previously qualified first16 pilot is inherited unchanged; next48 dense positions and360 sparse positions complete the424. Twenty-three sparse local16/8 certificates, exact full-provider equality and symbolic transport establish selected satisfaction, then exact aggregate component rows follow through the already qualified body theorem. Aggregate428rows repeat the shared copy; unique selected425rows are424arithmetic+onecopy. No desired selected-row truth/hash conclusion/local-checker result/new assignment caller premise. Fifty new modules369original reports plus one inherited module6original reports are separately accounted; inherited pilot is not freshly compiled or new source coverage. Actual complete path/root/hash semantics, concrete field/compiled relation instantiation, Boolean/integer/natural interpretation, lawful compatible seed/all assertion truth, native correspondence and full Transfer remain owned OPEN. Original1545attempt history147failures preserved; unchanged independently reviewed guards. Combined replay UNRUN.'
r=dict(status='PASSED',modules=51,reports=375,new_modules=50,new_reports=369,inherited_modules=1,inherited_reports=6,inherited_names=sorted(reused),source_pins=[e['source']for e in entries],arithmetic_positions_half_open=[3146,3570],unique_arithmetic_positions=424,copy_position=200769,unique_selected_rows=425,aggregate_component_rows=428,scope=scope,full_transfer='OPEN',root_verifier_execution='NONE');(D/'source-semantic-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k]for k in ['status','modules','reports','new_modules','new_reports','full_transfer']}))
