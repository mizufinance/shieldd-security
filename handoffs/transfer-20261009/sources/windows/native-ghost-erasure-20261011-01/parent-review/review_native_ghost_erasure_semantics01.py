"""Exact pure maintained repair replay, failed history and scoped model comparison review."""
from pathlib import Path
import ast,difflib,hashlib,json,re
J=Path(__file__).parent;D=J/'windows-native-ghost-erasure-review01';P=D/'packet01';Q=P/'rejected/source01';module='TransferNativeGhostErasure01'
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
old=(Q/'handwritten'/f'{module}.lean').read_text();source=P/'source/ShielddSecurity'/f'{module}.lean';new=source.read_text()
assert (Q/'handwritten'/f'{module}.lean').read_bytes()==(Q/'project/ShielddSecurity'/f'{module}.lean').read_bytes()
plan=json.loads((Q/'plan.json').read_bytes());assert pin(Q/'handwritten'/f'{module}.lean')['sha256']==plan['targets'][0]['source']['sha256']
headers=lambda t:[m.group(0).split(' := by')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^set_option pp.all|\Z)',t)]
assert len(headers(old))==4 and headers(old)==headers(new)
assert old.split('theorem bounded_primitive')[0]==new.split('theorem bounded_primitive')[0]
events=[json.loads(l)for l in(Q/'events.jsonl').read_text().splitlines()];assert len(events)==2
failed=events[-1]['result'];assert failed['status']=='failed'and failed['reason']=='Lean exit 1'and failed['seconds']<240
diagnostics=[l for l in(Q/'runs'/('01-'+module)/'stdout.txt').read_text().splitlines()if 'error:'in l or 'warning:'in l];assert diagnostics and not any('warning:'in l for l in diagnostics)
recipe=P/'qualified/prepare_recipe.py';nodes=ast.parse(recipe.read_text()).body;chosen=[];active=False
for n in nodes:
 if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='source'for t in n.targets)and not active:active=True;continue
 if active:
  if isinstance(n,ast.Expr):break
  assert isinstance(n,(ast.Assign,ast.Assert));chosen.append(n)
env={'source':old};exec(compile(ast.Module(body=chosen,type_ignores=[]),str(recipe),'exec'),env);assert chosen and env['source']==new
scope=[
 'Both comparison programs share the same ExtendedObject state, pending getter and primitive/native encodeNative, and all callbacks. Only the pending encoder differs: supported finite codec versus always-native sum branch. This is encoder/model outcome equality, not deletion of the entire ExtendedObject state type or a native Rust execution theorem.',
 'Given canonical input/start bounds and coherent/open/capacity invariant, all modeled primitive outcomes are identical, including errors and every returned cache. Successful inspection derives support, so unsupported encoder branch is unused.',
 'Note recursion ignores nullifier encoding; reshape and raw Transfer preserve every returned outcome with the same callbacks and observed effects. No successful-body or desired-result premise is supplied.',
 'Native typed codec/getter/Clone/imbl inputs/callback/key/trace/ownership/OS remain owned OPEN correspondence. Capability/delivery/index wrappers and whole reachable traces remain successor obligations. Full Transfer/native controls/final replay are not qualified here.'
]
report=dict(status='PASSED',kind='Independent complete source contract and maintained pure repair replay; no verifier/native launch',source=pin(source),recipe=pin(recipe),fresh_reports=5,definitions_and_all_four_contracts_unchanged=True,rejected=dict(source=pin(Q/'handwritten'/f'{module}.lean'),whole_attempt=failed,diagnostics=diagnostics,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True)))),contracts=scope,source_replay_exact=True,full_transfer='OPEN',native_execution='UNRUN');(D/'semantic-source-review01.json').write_text(json.dumps(report,indent=2)+'\n')
x=json.loads((D/'endpoint-audit-review01.json').read_bytes());x['semantic_scope']=scope;x['rejected']=[report['rejected']];x['precise_repair_review']=pin(D/'semantic-source-review01.json');(D/'endpoint-audit-review01.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(status='PASSED',fresh_reports=5,all_contracts_unchanged=True,pure_repair_replay=True,full_transfer='OPEN')))
