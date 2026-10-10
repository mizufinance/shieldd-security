"""Parent DATA inspection; no Lean invocation or proof credit."""
import sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
import hashlib, json
from pathlib import Path
R=Path(__file__).resolve().parents[2]
O=R/'outputs/mac-transfer-cut12'
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((O/'qualification-plan-manifest01.json').read_bytes())
for x in manifest['files']:
 p=R/x['path']; assert sha(p)==x['sha256'] and p.stat().st_size==x['bytes']
plan=json.loads((O/'budget-plan01.json').read_bytes())
cut=json.loads((O/'cut01.json').read_bytes())
parent=json.loads((R/'work/parent-upstream-cut-plan01/data-plan01.json').read_bytes())
for a,b in zip(cut['nodes'],parent['nodes'],strict=True):
 assert a==dict(source_node=b['id'],operation=b['op'],left=b['left'],right=b['right'],expression=dict(kind=b['kind'],terms=b['terms']),certificate=b['certificate'])
assert cut['constants']==[dict(id=x['id'],value=x['value']) for x in parent['constants']]
for a,b in zip(cut['indexed_original_rows'],parent['rows'],strict=True):
 assert a['capture_index']==b['id'] and a['unoutlined_a']==b['a'] and a['unoutlined_b']==b['b'] and a['origin']==b['origin']
assert cut['write_columns']==parent['writes'] and cut['source_input_columns']==[10,23,24]
compiler=R/'work/shared-build-handoff/circuits/ShielddSecurity/CompilerCompletion.lean'
t=compiler.read_text(); assert '| product (left right remainder : Linear) (output auxiliary : Nat)' in t and '| .product _ _ _ output auxiliary => [output, auxiliary]' in t
assert plan['counts']['product_constructor_steps']==2 and plan['counts']['joined_steps']==2+864+1==867 and plan['counts']['joined_rows']==4+1152+1==1157
limits=plan['limits']; assert limits['heap_MiB']==2048 and limits['seconds_per_module']==240 and limits['group_RSS_bytes']==4294967296 and limits['LEAN_NUM_THREADS']==1 and limits['no_escalation']
inh=json.loads((O/'inherited-qualification01.json').read_bytes())
assert inh['status']=='passed' and inh['old_stage_entries_rehashed']==392 and inh['kernel_runs']==0
for item in inh['reused'].values():
 assert sha(R/item['original_receipt_path'])==item['original_receipt_sha256']
result=dict(status='passed',plan_sha256=sha(O/'budget-plan01.json'),manifest_sha256=sha(O/'qualification-plan-manifest01.json'),descriptor_sha256=sha(O/'cut01.json'),parent_node_constant_row_data_equal=True,corrected_steps=dict(products=2,cut_with_copy=3,joined_with_shared_copy=867),joined_rows=1157,inherited_receipts_rehashed=len(inh['reused']),admission='First two named probe modules only; inspect actual cost before successor endpoint',kernel_runs=0,proof_credit=0,full_transfer='OPEN')
out=Path(__file__).with_name('parent-admission12.json'); assert not out.exists();out.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
