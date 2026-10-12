"""Independent registry captured-row/hash scope review; no verifier launch."""
from pathlib import Path
import json,hashlib,re
J=Path(__file__).resolve().parent;W=J.parent;D=J/'registry-global175-176-review01';P=W/'mac-registry-global175-176-kernel-result01';G=W/'shared-build-handoff'
entries=json.loads((P/'source-object-receipt01.json').read_text());assert len(entries)==34
sources={}
for e in entries:
 p=Path(e['source']['path']);b=p.read_bytes();assert len(b)==e['source']['bytes'] and hashlib.sha256(b).hexdigest()==e['source']['sha256'];sources[e['module']]=b.decode()
positions=[]
for i in range(26):
 n=f'CapturedRegistryGlobalBinding175G{i:02d}';s=sources[n];start=2306+16*i;positions.extend(range(start,start+16))
 assert 'satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770' in s and 'verifier_links rho satisfied' in s
 if i<20:
  assert f'(RegistryWhole23.selectedRows.drop {16*i}).take 16' in s and f"List.range' {start} 16" in s
  assert 'theorem checked : productionCheck=true := by decide +kernel' in s and 'indices rows checked rho' in s
 else:
  assert f'(RegistryWhole23.selectedRows.drop {16*i} |>.take 16)' in s and 'check_congr' in s and 'parent_equal' in s and 'all_goals rfl' in s
  nums=re.search(r'change position ∈ \[([^]]+)\]',s)[1];assert [int(x)for x in nums.split(',')]==list(range(start,start+16))
  local=sources[f'CapturedRegistrySparse244G{i:02d}'];assert f"List.range' {start} 16" in local and f'originalRows.drop {16*i-44}' in local
  assert 'CompilerWindowRenaming05.swap 23076 396 1988' in local and 'theorem local_checked : localCheck=true := by decide +kernel' in local
  assert [int(x)for x in re.findall(r'^ \| (\d+) => some',local,re.M)]==list(range(start,start+16))
assert positions==list(range(2306,2722))
s=sources['CapturedRegistryGlobalBinding175'];assert 'RegistryWhole23.selectedRows.take 416' in s and '[16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16,16]' in s
assert 'chunks.flatten=arithmeticRows' in s and 'arithmeticRows++[TransferPoseidonCall04Shared01.rawCopy]=RegistryWhole23.selectedRows' in s
assert 'CapturedFullRelation58.rowAt 200770 200769' in s and 'copy_checked' in s and 'arithmetic_sound rho satisfied' in s
for i in range(26):assert f'CapturedRegistryGlobalBinding175G{i:02d}.sound rho satisfied' in s
s=sources['CapturedRegistryGlobalSound176'];assert '(one : rho 0=1)' in s and '(satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770)' in s
assert 'eval rho RegistryWhole23.actualResult=Poseidon.hash6' in s and '(RegistryInputJoin24.semanticInputs rho)' in s
for n in ['CapturedPriorGlobalBinding170','CapturedThreeCallGlobalBinding173','CapturedRegistryGlobalBinding175']:assert n+'.sound rho satisfied' in s
assert 'RegistryInputJoin24.arbitrary_registry rho one' in s
graph=json.loads((J/'source-integration-20261011-01/mac-source-closure1690.json').read_text())['custom_sources'];inherited={}
for name in ['RegistryInputJoin24','RegistryWhole23']:
 v=graph[name];p=G/v['published_paths'][0];b=p.read_bytes();assert len(b)==v['bytes'] and hashlib.sha256(b).hexdigest()==v['sha256'];inherited[name]=b.decode()
s=inherited['RegistryInputJoin24'];assert '[rho 11,rho 12,rho 13,' in s
for term in ['23 [rho 14,rho 15,rho 21,rho 22]','24 [rho 23,rho 24,rho 30,rho 31,rho 32,rho 33]','36 [rho 34,rho 35,rho 36,rho 42,rho 43]','(prior : Satisfies rho CapturedPriorRows16Frame01.capturedPriorRows)','(joined : Satisfies rho TransferPoseidonThreeCallJoin15Program01.originalRows)','(leaf : Satisfies rho RegistryWhole23.selectedRows)']:assert term in s
data=G/'handoffs/transfer-20261009/sources/mac/registry-leaf23/generator-input/actual-result-data01.json';v=json.loads(data.read_text());assert v['raw']==28925
terms=re.search(r'def actualResult : Linear := (\[[^\n]+\])',inherited['RegistryWhole23'])[1];assert [[int(a),int(b)]for a,b in re.findall(r'\((\d+),(\d+)\)',terms)]==v['actual_terms']
aud=json.loads((D/'audit-result01.json').read_text());assert aud['declarations']==222
scope='Full captured relation satisfaction and rho0=1 derive the exact registry hash expression from original inputs, including first and nested child hashes. All416 actual registry arithmetic positions2306..2721 plus copy200769 are derived through checked finite row associations; earlier0..2305 arithmetic bindings are inherited exact qualifications. Dense320 and sparse96 certificates partition the new416 positions. Six sparse local providers are proved equal to full rowAt on precisely their indices; full relation remains the soundness antecedent, with copy links derived from it. No desired hash, selected-row satisfaction, local checker result or new assignment is a caller premise. Exact actualResult terms match the previously independently reviewed raw node28925. Abstract Field/CharP and exact captured row semantics are the declared domain; concrete field/compiled relation instantiation, complete Merkle path/anchor/root, legal seed/all assertion truth, native correspondence and full Transfer remain owned OPEN. Combined kernel replay UNRUN. Guard267 archive-original reappearance gap and independent reproducer are retained explicitly. Root guard review26 authenticates historical exact bytes/absence and the repaired successor; physical limits unchanged, no accepted proof replay.'
r=dict(status='PASSED',modules=34,reports=222,source_pins=[e['source']for e in entries],new_arithmetic_half_open=[2306,2722],unique_new_arithmetic_positions=416,prior_arithmetic_half_open=[0,2306],connected_unique_arithmetic_positions=2722,copy_position=200769,actual_result_raw_node=28925,scope=scope,full_transfer='OPEN',root_verifier_execution='NONE',guard_review='PASSED26_SUCCESSOR_AND_HISTORICAL_RECONCILIATION')
(D/'source-semantic-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k]for k in ['status','modules','reports','unique_new_arithmetic_positions','full_transfer','guard_review']}))
