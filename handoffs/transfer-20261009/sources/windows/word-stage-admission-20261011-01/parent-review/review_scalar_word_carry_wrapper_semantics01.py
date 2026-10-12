"""Exact source contract/failure/maintained pure repair replay for scalar source models."""
from pathlib import Path
import argparse,ast,difflib,hashlib,json,re
J=Path(__file__).parent
p=argparse.ArgumentParser();p.add_argument('label');p.add_argument('module');p.add_argument('rejected');p.add_argument('reports',type=int);p.add_argument('definitions',type=int);p.add_argument('theorems',type=int);a=p.parse_args();D=J/f'windows-{a.label}-review01';P=D/'packet01';Q=P/'rejected'/a.rejected
sha=lambda b:hashlib.sha256(b).hexdigest()
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=sha(b))
source=P/'source/ShielddSecurity'/f'{a.module}.lean';old=(Q/'handwritten'/f'{a.module}.lean').read_text();new=source.read_text();assert(Q/'project/ShielddSecurity'/f'{a.module}.lean').read_text()==old
headers=lambda t:[m.group(0).split(' := by')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',t)]
definitions=lambda t:[m.group(0)for m in re.finditer(r'(?m)^def [\s\S]*?(?=^def |^theorem |^set_option pp.all|\Z)',t)]
assert len(headers(old))==a.theorems and headers(old)==headers(new);assert len(definitions(old))==a.definitions and definitions(old)==definitions(new);assert a.reports==a.definitions+a.theorems
recipe=P/'qualified/prepare_recipe.py';nodes=ast.parse(recipe.read_text()).body;chosen=[]
for i,n in enumerate(nodes):
 if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='a'for t in n.targets)and isinstance(n.value,ast.Constant)and isinstance(n.value.value,str)and n.value.value in old:
  segment=nodes[i:i+3];assert isinstance(segment[1],ast.Assert)and isinstance(segment[2],ast.Assign);chosen.extend(segment)
assert chosen;env={'s':old};exec(compile(ast.Module(body=chosen,type_ignores=[]),str(recipe),'exec'),env);assert env['s']==new
e=[json.loads(l)for l in(Q/'events.jsonl').read_text().splitlines()];assert len(e)==2;failed=e[-1]['result'];assert failed['status']=='failed'and failed['reason']=='Lean exit 1'and 0<failed['seconds']<240
log=Q/f'runs/01-{a.module}/stdout.txt';oldplan=json.loads((Q/'plan.json').read_bytes());assert pin(Q/'handwritten'/f'{a.module}.lean')['sha256']==oldplan['targets'][0]['source']['sha256']
freshplan=json.loads((P/'qualified/plan.json').read_bytes());identity=[q for q in freshplan['pins']if q['path'].endswith('stdout.txt')and ('transfer-'+a.label+'-20261011-'+a.rejected)in q['path']];assert len(identity)==1 and pin(log)['bytes']==identity[0]['bytes']and pin(log)['sha256']==identity[0]['sha256'];diagnostics=[l for l in log.read_text().splitlines()if 'error:'in l or 'warning:'in l];assert diagnostics
scopes={'scalar-word-primitives':'UInt64 packing supplies raw range; BitVec128 widened MAC and low/high split conserve full integer without overflow. Actual Rust evaluation, carry schedule/subtraction/byte layout/congruence/type invariant remain owned OPEN.','scalar-carry-schedule':'Model UInt64 MAC loop preserves exact limb count and full positional integer including final carry. Dropping low output and appending final carry derives exact radix quotient for any nonempty vector; no supplied quotient premise. Actual Rust trace/ADC/SBB/byte layout remain owned OPEN.','scalar-four-round-wrapper':'Exact source modulus/inverse u64 constants, derived wrapped low-word multipliers and four finite carry rounds compose to symbolic recurrence. Four-word width and multiplier bounds/count derive from actual modeled calls. Final mathematical conditional subtraction gives canonical field range. Actual native padded eight-limb/ADC/SBB/carry trace, sub-mask/endian/type/modular correspondence remain owned OPEN.'}
r=dict(status='PASSED',kind='Independent complete source contracts, exact failed-history and maintained pure source repair; no verifier/native launch',source=pin(source),recipe=pin(recipe),fresh_reports=a.reports,definitions=a.definitions,theorems=a.theorems,all_model_definitions_and_contracts_unchanged=True,pure_source_repair_exact=True,rejected=dict(source=pin(Q/'handwritten'/f'{a.module}.lean'),result=failed,diagnostics=diagnostics,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True)))),scope=scopes[a.label],full_transfer='OPEN',native_execution='UNRUN')
out=D/'semantic-replay-review01.json';assert not out.exists();out.write_text(json.dumps(r,indent=2)+'\n')
if not(D/'semantic-source-review01.json').exists():
 (D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');x=json.loads((D/'endpoint-audit-review01.json').read_bytes());x['rejected']=[r['rejected']];x['semantic_scope']=r['scope'];x['precise_repair_review']=pin(out);(D/'endpoint-audit-review01.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(status='PASSED',module=a.module,reports=a.reports,pure_repair=True)))
