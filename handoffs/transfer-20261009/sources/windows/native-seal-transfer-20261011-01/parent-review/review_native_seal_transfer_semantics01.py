"""Independent exact maintained-source repair and endpoint scope review; no builds."""
from pathlib import Path
import ast, difflib, hashlib, json, re
J=Path(__file__).parent; D=J/'windows-native-seal-transfer-review01'; P=D/'packet01'
def read(p):return json.loads(p.read_bytes())
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
module='TransferNativeSealTransfer01'; target=P/'source/ShielddSecurity'/f'{module}.lean'; current=target.read_text()
old=P/'preserved/source02'; previous=(old/'handwritten'/f'{module}.lean').read_text()
assert previous==(old/'project/ShielddSecurity'/f'{module}.lean').read_text()
plan=read(old/'plan.json'); assert len(plan['targets'])==1
assert pin(old/'handwritten'/f'{module}.lean')['sha256']==plan['targets'][0]['source']['sha256']
events=[json.loads(l)for l in(old/'events.jsonl').read_text().splitlines()]
assert len(events)==2 and events[-1]['result']['status']=='failed' and events[-1]['result']['reason']=='Lean exit 1'
assert events[-1]['result']['seconds']<240
diagnostics=[l for l in(old/'runs'/('01-'+module)/'stdout.txt').read_text().splitlines()if 'error:'in l or 'warning:'in l]
assert len(diagnostics)==1 and 'Tactic `rewrite` failed' in diagnostics[0] and not any('warning:'in l for l in diagnostics)
# Replay only the maintained source transformations, never its preparations or verifier calls.
recipe=P/'qualified/prepare_recipe.py'; nodes=ast.parse(recipe.read_text()).body; chosen=[]; active=False
for node in nodes:
 if isinstance(node,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='source'for t in node.targets)and not active:
  active=True; continue
 if active:
  if isinstance(node,ast.Expr):break
  assert isinstance(node,(ast.Assign,ast.Assert))
  chosen.append(node)
assert chosen
scope={'source':previous};exec(compile(ast.Module(body=chosen,type_ignores=[]),str(recipe),'exec'),scope)
assert scope['source']==current
def contracts(text):return [m.group(0).split(' := by')[0] for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^set_option pp.all|\Z)',text)]
normalize=lambda s:s.replace('∃ frozen, frozen.insertions.accepted','∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted')
assert len(contracts(previous))==3 and list(map(normalize,contracts(previous)))==contracts(current)
assert not re.findall(r'(?m)^(?:def|abbrev|structure|inductive|axiom) ',current)
unrun=P/'preserved/source01';assert not list(unrun.rglob('events.jsonl'))
assert (unrun/'handwritten'/f'{module}.lean').read_bytes()==(unrun/'project/ShielddSecurity'/f'{module}.lean').read_bytes()
contracts_scope=[
 'Modeled source seal at a state with actual pending invariant and canonical field bounds stores the supported native sealed ordered vector. The predicate is not a native execution theorem.',
 'Actual model returned state transfer preserves the reached finalization object under a pointwise field correspondence at that specific height/state/queue, not a universal ghost-state callback contract.',
 'Whole bounded default walk plus successful pipeline derives the actual transferred sealed allInputs vector, uniqueness/cap/canonical bounds, exact Frozen accepted inputs/root/Ready/Idle and observed roots/boundary. The desired vector is derived from the walk and supported-only getter, not supplied by the finalization premise.',
 'Supported primitive roundtrip, action input projections, key representation injectivity, pointwise finalization field correspondence and supported getter are still owned native correspondence interfaces; no native control or full Transfer closure follows.',
 'Internal writes during failed child execution remain a successor obligation. Native typed/Clone/Any/Arc, imbl collections, ownership/locks, snapshots/ICS23, temporal/partition/OS and genuine replay are still open.'
]
report=dict(status='PASSED',kind='Independent maintained source repair replay and semantic scope review; no Lean/native execution',source=pin(target),recipe=pin(recipe),fresh_complete_reports=3,contracts=contracts_scope,rejected=dict(original_source=pin(old/'handwritten'/f'{module}.lean'),whole_attempt=events[-1]['result'],diagnostics=diagnostics,all_three_contracts_preserved_with_explicit_intended_Frozen_type=True,exact_delta=''.join(difflib.unified_diff(previous.splitlines(True),current.splitlines(True)))),withdrawn_unrun=dict(source=pin(unrun/'handwritten'/f'{module}.lean'),qualification=False,scope='Original universal frame/getter draft intentionally withdrawn before execution; source02 narrows both to actual reached/supported contracts.'),full_transfer='OPEN',native_execution='UNRUN')
(D/'semantic-source-review01.json').write_text(json.dumps(report,indent=2)+'\n')
a=read(D/'endpoint-audit-review01.json');a['semantic_scope']=contracts_scope;a['preserved_history_review']=pin(D/'semantic-source-review01.json');(D/'endpoint-audit-review01.json').write_text(json.dumps(a,indent=2)+'\n')
print(json.dumps(dict(status='PASSED',fresh_reports=3,failed_attempt_preserved=True,maintained_source_transform_replayed=True,full_transfer='OPEN')))
