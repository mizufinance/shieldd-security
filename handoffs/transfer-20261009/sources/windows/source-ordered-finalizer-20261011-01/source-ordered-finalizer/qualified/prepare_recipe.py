"""Fresh guarded retry after physical-pressure stop; no source/guard changes."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
old=DIAG/'transfer-source-ordered-finalizer-20261011-02'
s=(old/'prepare_recipe.py').read_text().replace('transfer-source-ordered-finalizer-owned-floor-20261011-02','transfer-source-ordered-finalizer-owned-floor-20261011-03')
exec(compile(s,str(old/'prepare_recipe.py'),'exec'),{'__file__':str(ROOT/'prepare_recipe.py'),'__name__':'__main__'})
assert (ROOT/'handwritten/TransferSourceOrderedFinalizer01.lean').read_bytes()==(old/'handwritten/TransferSourceOrderedFinalizer01.lean').read_bytes()
# Reauthenticate the source positions independently of the old inventory table.
shape=json.loads((ROOT/'context/corrected-finalization-call-order.json').read_text())
texts={}
for row in shape['runtime_sources']:
    data=Path(row['path']).read_bytes();assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'];texts[row['path']]=data.decode()
tree=next(t for p,t in texts.items() if p.endswith('component\\tree.rs'))
manager=next(t for p,t in texts.items() if p.endswith('component\\manager.rs'))
body=manager[manager.index('    async fn finalize_compact_block('):]
calls=['.end_sct_block(end_epoch)','self.pending_user_registrations()','self.pending_user_status_changes()','self.pending_asset_registrations()','self.object_delete(state_key::pending_routing_actions());']
positions=[body.index(c) for c in calls];assert positions==shape['call_positions']==sorted(positions)
a=tree.index('    async fn end_sct_block(');b=tree.index('    fn write_sct_cache(',a);sct=tree[a:b]
assert sct.index('self.ensure_nullifier_block_sealed()?;')<sct.index('self.object_delete(state_key::cache::block_materialization());')<sct.index('self.write_sct(height, tree, block_root, epoch_root).await;')
a=tree.index('    async fn write_sct(');b=tree.index('    async fn prune_sct_history(',a);assert 'self.write_sct_cache(sct);' in tree[a:b]
p=ROOT/'prepare.py';s=p.read_text();at=s.index("plan['artifact_policy']")
s=s[:at]+"pressureOrdered=DIAG/'transfer-source-ordered-finalizer-20261011-02'\nplan['pins'] += [pin(pressureOrdered/n) for n in ['prepare_recipe.py','recipe_source.py','prepare.py','plan.json','review.json','execute_bounded.py','source-mapping.json','events.jsonl','context/corrected-finalization-call-order.json','handwritten/TransferSourceOrderedFinalizer01.lean','project/ShielddSecurity/TransferSourceOrderedFinalizer01.lean','runs/01-TransferSourceOrderedFinalizer01/stdout.txt']]\n"+s[at:]
p.write_text(s)
