"""Independent typed layered object/SCT model review and original histories; no builds."""
from pathlib import Path
import argparse,json,hashlib,re,difflib
J=Path(__file__).resolve().parent
cases={
 'pending-saturating-capacity':('TransferPendingSaturatingCapacity01',5),
 'word-layered-object-read':('TransferWordLayeredObjectRead01',8),
 'word-layer-flatten':('TransferWordLayerFlatten01',4),
 'word-object-put':('TransferWordObjectPut01',8),
 'word-sct-pending-read':('TransferWordSctPendingRead01',8),
}
p=argparse.ArgumentParser();p.add_argument('label',choices=cases);a=p.parse_args();M,N=cases[a.label];D=J/('windows-'+a.label+'-review01');P=D/'packet01';S=P/'source/ShielddSecurity'/(M+'.lean');final=S.read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
plan=json.loads((P/'qualified/plan.json').read_text());target=plan['targets'][0]['source'];assert len(S.read_bytes())==target['bytes'] and hashlib.sha256(S.read_bytes()).hexdigest()==target['sha256']
maintained=[z for z in plan['pins'] if z['path'].replace('\\','/').endswith('/handwritten/'+M+'.lean')];assert any(z['bytes']==target['bytes'] and z['sha256']==target['sha256'] for z in maintained)
assert re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',final,re.M)==re.findall(r'^#check @([^\n]+)',final,re.M)
assert len(re.findall(r'^#check @',final,re.M))==N
W=J.parent/'runtime-snapshot';delta=(W/'third_party/cnidarium-0.83.0/src/delta.rs').read_text();tree=(W/'crates/core/component/sct/src/component/tree.rs').read_text()
associations=[]
for name in ['saturating-capacity-shape.json','checked-pending-read-shape.json','checked-pending-put-shape.json','sct-pending-read-shape.json']:
 f=P/'context'/name
 if not f.exists():continue
 x=json.loads(f.read_text());assert x['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
 rows=x.get('runtime_sources',[x['runtime_source']] if 'runtime_source'in x else [])
 for z in rows:
  rel=z['path'].replace('\\','/').split('/shieldd-pr160-844389ee/')[1];b=(W/rel).read_bytes();assert len(b)==z['bytes']and hashlib.sha256(b).hexdigest()==z['sha256']
 if name=='saturating-capacity-shape.json':
  assert tree[tree.index('async fn stage_nullifiers'):tree.index('pub const SCT_BLOCK_COMMITMENT_CAPACITY')]==x['source_stage_body'];assert x['source_consensus_limit']=='pub const MAX_NULLIFIERS_PER_BLOCK: usize = 32_768;' and x['source_consensus_limit'] in tree
  assert 'ordered.len().saturating_add(nullifiers.len()) <= MAX_NULLIFIERS_PER_BLOCK' in x['source_stage_body']
 elif name=='checked-pending-read-shape.json':
  start=delta.index('    fn object_get<T:');body=delta[start:delta.index('    fn prefix_raw(',start)];stage=tree[tree.index('async fn stage_nullifiers'):tree.index('pub const SCT_BLOCK_COMMITMENT_CAPACITY')]
  assert body==x['object_get_body']and stage==x['pending_stage_body'];assert body.index('leaf_cache')<body.index('for layer in self.layers.iter().rev()')<body.index('self.state');assert body.count('downcast_ref().unwrap_or_else(|| panic!')==2
 elif name=='checked-pending-put-shape.json':
  start=delta.index('    fn object_type(');body=delta[start:delta.index('    fn object_get<T:',start)];start=delta.index('    fn object_put<T:');put=delta[start:delta.index('    fn object_delete(',start)]
  assert body==x['source_object_type_body']and put==x['source_object_put_body'];assert body.index('leaf_cache')<body.index('for layer in self.layers.iter().rev()')<body.index('self.state');assert put.index('self.object_type(key)')<put.index('panic!')<put.index('.insert(key, Some(Box::new(value)))')
 else:
  enum=tree[tree.index('pub(super) enum PendingNullifierBlock'):tree.index('async fn stage_nullifiers')];body=tree[tree.index('    fn pending_nullifiers('):tree.index('impl<T: StateRead + ?Sized> SctRead for T {}')]
  assert enum==x['source_pending_enum_and_methods']and body==x['source_pending_read_methods'];assert 'None | Some(PendingNullifierBlock::Sealed { .. }) => Ok(())'in body and '.map(|pending| pending.ordered().clone())'in body
 associations.append(pin(f))
repairs={
 'word-object-put':('exact ⟨by simp only [ite_true], fun other different => by simp only [if_neg different]⟩','exact ⟨if_pos rfl, fun _ different => if_neg different⟩'),
 'word-layer-flatten':('    change selectedLiveLayers ((rest.map (fun item => item.objects)).reverse)\n      (applyCache parent layer).objects key = (applyLayers (applyCache parent layer) rest).objects key','    have singleton : (fun k => selectedLiveLayers [layer.objects] parent.objects k) = (applyCache parent layer).objects := by\n      funext k\n      cases selected : layer.objects k <;> simp only [selectedLiveLayers, applyCache, overlay, selected]\n    rw [singleton]'),
}
records=[]
for q in sorted((P/'unselected').glob('*')):
 old=(q/'handwritten'/(M+'.lean')).read_text();assert old==(q/'project/ShielddSecurity'/(M+'.lean')).read_text()
 events=[json.loads(l)for l in(q/'events.jsonl').read_text().splitlines()];assert len(events)==2;r=events[-1]['result'];assert r['status']=='failed'and r['seconds']<240
 assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes();assert json.loads((q/'plan.json').read_text())['pressure_limits']==json.loads((P/'qualified/plan.json').read_text())['pressure_limits']
 if r['reason']=='Physical memory pressure':
  assert old==final and not list(q.glob('runs/*/stdout.txt'))
 else:
  assert a.label in repairs and r['reason']=='Lean exit 1';before,after=repairs[a.label];assert old.count(before)==1 and old.replace(before,after)==final
  logs=list(q.glob('runs/*/stdout.txt'));assert len(logs)==1 and 'error:'in logs[0].read_text()
 records.append(dict(kind='Original failed attempt; no accepted result',result=r,source=pin(q/'handwritten'/(M+'.lean')),events=pin(q/'events.jsonl'),exact_delta=''.join(difflib.unified_diff(old.splitlines(True),final.splitlines(True))),all_definitions_and_theorem_contracts_unchanged=True))
scopes={
 'pending-saturating-capacity':'Finite min(sum,2^bits-1) model derives exact unbounded natural acceptance when capacity is below ceiling; consensus32768 headroom proved for32/64bits. Accepted gate yields both length bounds, without initial length or desired sum assumption. Native usize ABI/operator and actual vector lengths remain explicit correspondence obligations.',
 'word-layered-object-read':'Source-shaped leaf/newest-to-oldest finite stack lookup derives selected entry from live stack recurrence. Missing applied cache/parent and wrong selected type panic; tombstone stops/defaults, map miss continues. Model liveness is explicit, no successful getter or chosen entry caller premise.',
 'word-layer-flatten':'Constructed live stack in newest-first lookup equals original functional oldest-first applyLayers and exact flatten object observation. No selected object/getter success premise; result may still panic on selected wrong type. Existing layer liveness is an explicit model domain.',
 'word-object-put':'Fixed pending-enum TypeId abstraction checks previously selected type before inserting. Absent/tombstone and previous Open/Sealed permit insert; other type panics. Returned checked insertion derives exact latest write and frames all other keys; supported canonical bounded sealed put derives successful checked getter. Successful returned put is an explicit execution premise, while resulting write/getter is derived.',
 'word-sct-pending-read':'Three SCT getters retain original ordered canonical fields and distinguish absent/Open/Sealed/wrong type. Absence passes ensure-sealed while isSealed is false; ensure success alone does not imply present sealed. Outer nonreturning panic sentinel is distinct from inner returned open-block refusal.',
}
scope=scopes[a.label]+' Exact locked Rust snippet association is static. Actual Any/TypeId/downcast/Clone/boxing/locks/imbl/private Scalar/compiler/ownership/liveness/concurrency/full trace remains owned OPEN; model panic sentinel is not an executed native control. Full Transfer OPEN.'
r=dict(status='PASSED_SOURCE_HISTORY',kind='Handwritten model scope, exact locked snippets and original failed history; no verifier',source=pin(S),fresh_reports=N,rejected=records,static_associations=associations,scope=scope,full_transfer='OPEN',native_execution='UNRUN');(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(label=a.label,status=r['status'],reports=N,history=len(records))))
