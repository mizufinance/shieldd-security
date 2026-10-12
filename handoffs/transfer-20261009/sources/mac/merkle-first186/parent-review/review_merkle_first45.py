"""Exact initial Merkle selection/hash captured-row coverage; no verifier."""
from pathlib import Path
import json,hashlib,re
J=Path(__file__).resolve().parent;W=J.parent;D=J/'merkle-first186-review01';P=W/'mac-merkle-first186-kernel-result01';entries=json.loads((P/'source-object-receipt01.json').read_text());assert len(entries)==39;sources={}
for e in entries:
 p=Path(e['source']['path']);b=p.read_bytes();assert len(b)==e['source']['bytes']and hashlib.sha256(b).hexdigest()==e['source']['sha256'];sources[e['module']]=b.decode()
positions=[]
for i in range(26):
 n=f'CapturedMerkleFirstGlobal186B{i:02d}';s=sources[n];start=2734+16*i;count=16 if i<25 else 12;positions.extend(range(start,start+count));assert 'satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770' in s and 'verifier_links rho satisfied' in s
 if i<15:
  assert f'MerkleHash27Whole.selectedRows.drop {16*i} |>.take {count}' in s and f"List.range' {start} {count}" in s
  assert 'theorem checked : productionCheck=true := by decide +kernel' in s
 else:
  assert f'(MerkleHash27Whole.selectedRows.drop {16*i} |>.take {count})' in s and 'check_congr' in s and 'parent_equal' in s and 'all_goals rfl' in s
  nums=re.search(r'change position ∈ \[([^]]+)\]',s)[1];assert [int(x)for x in nums.split(',')]==list(range(start,start+count))
  local=sources[f'CapturedMerkleFirstSparse245B{i:02d}'];assert f"List.range' {start} {count}" in local and f'originalRows.drop {16*i-40}' in local
  assert 'CompilerWindowRenaming05.swap 25064 396 424' in local and 'CompilerWindowRenaming05.swap 23076 396 1988' in local
  assert 'theorem local_checked : localCheck=true := by decide +kernel' in local
  assert [int(x)for x in re.findall(r'^ \| (\d+) => some',local,re.M)]==list(range(start,start+count))
assert positions==list(range(2734,3146))
s=sources['CapturedMerkleFirstSelection186'];assert "List.range' 2722 12++[200769]" in s and 'indices MerkleSelection26Data.originalRows' in s and 'theorem checked : productionCheck=true := by decide +kernel' in s and 'satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770' in s
s=sources['CapturedMerkleFirstGlobal186'];widths=re.search(r'slicesAt MerkleHash27Whole.selectedRows 0 \[([^]]+)\]',s)[1];assert list(map(int,widths.split(',')))==[16]*25+[12]
for t in ['chunks.flatten=MerkleHash27Whole.selectedRows.take 412','[200769] (MerkleHash27Whole.selectedRows.drop 412)','theorem copy_checked : copyCheck=true := by decide +kernel','←List.take_append_drop 412 MerkleHash27Whole.selectedRows','CapturedRegistryGlobalSound176.row_families rho satisfied','CapturedMerkleFirstSelection186.sound rho satisfied']:assert t in s
for i in range(26):assert f'CapturedMerkleFirstGlobal186B{i:02d}.sound rho satisfied' in s
aud=json.loads((D/'audit-result01.json').read_text());assert aud['declarations']==266
for name in ['source-generation-review01.json','source-history-review01.json']:assert json.loads((D/name).read_text())['status']=='PASSED'
graph=json.loads((J/'source-integration-20261011-01/mac-source-closure1724.json').read_text())['custom_sources'];imp=json.loads((D/'import-guard-review01.json').read_text());assert not(set(imp['custom_associations'])-set(graph)-set(sources))
scope='Exact initial Merkle captured-row transport: all412 hash arithmetic positions2734..3145, all12 selection arithmetic positions2722..2733, and the single shared copy200769. Dense240 plus sparse172 certificates cover exactly412 hash rows; the eleven sparse full-provider equalities and checked local certificates replace the retained heap-limited attempt. Full captured relation satisfaction on the same arbitrary assignment derives both all selected first-hash rows and inherited prior734/three-call/registry/selection row families. Connected earlier arithmetic0..2721 plus this424 yields3146 unique arithmetic positions; repeated component copy rows contribute one distinct position. No desired selected satisfaction, hash conclusion, local checker result or new assignment caller premise. Abstract Field/CharP and exact captured row interpretation are explicit domain; this packet proves row coverage, not the complete Merkle hash/path/root semantics. Remaining captured levels, Boolean/integer/natural interpretation, concrete field/compiled relation instantiation, lawful seed/all assertion truth, native correspondence and full Transfer remain owned OPEN. Original1495-attempt history includes147failed attempts, retained without replay. Guard26 archive-absence and guard27 exact raw-link census changes independently reviewed with unchanged physical limits. Combined replay UNRUN.'
r=dict(status='PASSED',modules=39,reports=266,source_pins=[e['source']for e in entries],hash_positions_half_open=[2734,3146],selection_positions_half_open=[2722,2734],unique_new_arithmetic_positions=424,connected_unique_arithmetic_positions=3146,copy_position=200769,hash_dense_positions=240,hash_sparse_positions=172,scope=scope,full_transfer='OPEN',root_verifier_execution='NONE');(D/'source-semantic-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k]for k in ['status','modules','reports','unique_new_arithmetic_positions','full_transfer']}))
