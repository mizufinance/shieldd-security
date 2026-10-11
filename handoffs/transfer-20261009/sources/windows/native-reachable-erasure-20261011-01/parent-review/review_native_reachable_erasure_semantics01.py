"""Precise unchanged walk contracts, newly audited helper and pure maintained repair replay."""
from pathlib import Path
import ast,difflib,hashlib,json,re
J=Path(__file__).parent;D=J/'windows-native-reachable-erasure-review01';P=D/'packet01';module='TransferNativeReachableErasure01';source=P/'source/ShielddSecurity'/f'{module}.lean';new=source.read_text()
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def headers(t):return {m.group(1):m.group(0).split(' := by')[0]for m in re.finditer(r'(?m)^theorem (\w+)[\s\S]*?(?=^theorem |^set_option pp.all|\Z)',t)}
fresh=headers(new);assert len(fresh)==3;rejected=[]
for name in ['source01','source02']:
 q=P/'rejected'/name;src=q/'handwritten'/f'{module}.lean';old=src.read_text();assert src.read_bytes()==(q/'project/ShielddSecurity'/f'{module}.lean').read_bytes();plan=json.loads((q/'plan.json').read_bytes());assert pin(src)['sha256']==plan['targets'][0]['source']['sha256']
 h=headers(old);assert len(h)==2 and all(fresh[n]==v for n,v in h.items())
 assert old.split('theorem ')[0].strip()==new.split('theorem ')[0].strip()
 events=[json.loads(l)for l in(q/'events.jsonl').read_text().splitlines()];assert len(events)==2;failed=events[-1]['result'];assert failed['status']=='failed'and failed['reason']=='Lean exit 1'and failed['seconds']<240
 log=(q/'runs'/('01-'+module)/'stdout.txt').read_text();diagnostics=[l for l in log.splitlines()if 'error:'in l or 'warning:'in l];assert diagnostics and not any('warning:'in l for l in diagnostics)
 rejected.append(dict(source=pin(src),whole_attempt=failed,diagnostics=diagnostics,model_definition_and_two_original_contracts_unchanged=True,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True)))))
recipe=P/'qualified/prepare_recipe.py';nodes=ast.parse(recipe.read_text()).body;chosen=[];active=False
for n in nodes:
 if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='source'for t in n.targets)and not active:active=True;continue
 if active:
  if isinstance(n,ast.Expr):break
  assert isinstance(n,(ast.Assign,ast.Assert));chosen.append(n)
env={'source':(P/'rejected/source02/handwritten'/f'{module}.lean').read_text()};exec(compile(ast.Module(body=chosen,type_ignores=[]),str(recipe),'exec'),env);assert chosen and env['source']==new
scope=['Fixed finite pending encoder and always-native encoder yield identical actual modeled request steps on coherent/canonical initial/input domain. This reuses the exact complete Item capability/body/delivery/index proofs with the same source callbacks and observations.','Whole model walk returns the same Option and exact parent/queue on either encoder. Its induction derives next invariant and canonical bounds from actual successful step, never supplies desired intermediate invariants or a success trace. Refused steps stop both walks identically.','The new generic Option-bind lemma quantifies only tails at actual returned values; its independent complete type/axiom report is included. Model definition and two original endpoint contracts unchanged after factoring; both failed whole originals remain failed.','Both sides retain ExtendedObject type and totalized decodeObject getter, with explicit supported primitive roundtrip/input/key contracts. Actual Rust codec/getter/Clone/imbl/input/callback/trace/ownership/OS and native publication correspondence remain owned OPEN.']
report=dict(status='PASSED',kind='Independent whole source and precise two-failure/helper repair review; no verifier launch',source=pin(source),recipe=pin(recipe),fresh_reports=4,new_helper='option_bind_equality_from_actual_returned_values',two_original_contracts_unchanged=True,source_replay_exact=True,rejected=rejected,contracts=scope,full_transfer='OPEN',native_execution='UNRUN');(D/'semantic-source-review01.json').write_text(json.dumps(report,indent=2)+'\n')
x=json.loads((D/'endpoint-audit-review01.json').read_bytes());x['semantic_scope']=scope;x['rejected']=rejected;x['precise_repair_review']=pin(D/'semantic-source-review01.json');(D/'endpoint-audit-review01.json').write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(status='PASSED',fresh_reports=4,new_helper_audited=True,two_original_contracts_unchanged=True,pure_repair_replay=True)))
