"""Exact two-rejection maintained proof repair chain; no preparer IO/builds."""
from pathlib import Path
import ast,difflib,json,hashlib,re
J=Path(__file__).parent;D=J/'windows-source-typed-input-projection-review01';P=D/'packet01';module='TransferSourceTypedInputProjection01';source=P/'source/ShielddSecurity'/(module+'.lean');final=source.read_text();fresh=json.loads((P/'qualified/plan.json').read_bytes())
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
headers=lambda s:[m.group(0).split(' := by')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',s)]
defs=lambda s:[m.group(0)for m in re.finditer(r'(?m)^def [\s\S]*?(?=^def |^theorem |^set_option pp.all|\Z)',s)]
assert len(headers(final))==3 and len(defs(final))==3
records=[]
for n,nextpath,recipe in [('01',P/'rejected/02/handwritten'/(module+'.lean'),P/'rejected/02/prepare_recipe.py'),('02',source,P/'qualified/prepare_recipe.py')]:
 q=P/'rejected'/n;old=(q/'handwritten'/(module+'.lean')).read_text();new=nextpath.read_text();assert old==(q/'project/ShielddSecurity'/(module+'.lean')).read_text();assert headers(old)==headers(final)and defs(old)==defs(final)
 nodes=ast.parse(recipe.read_text()).body;selected=[]
 for i,node in enumerate(nodes):
  if isinstance(node,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='a'for t in node.targets)and isinstance(node.value,ast.Constant)and isinstance(node.value.value,str)and node.value.value in old:
   segment=nodes[i:i+3];assert isinstance(segment[1],ast.Assert)and isinstance(segment[2],ast.Assign);assert ast.dump(segment[2].value)==ast.dump(ast.parse('s.replace(a, '+repr(segment[2].value.args[1].value)+')',mode='eval').body);selected.extend(segment)
 assert len(selected)==3;env={'s':old};exec(compile(ast.Module(body=selected,type_ignores=[]),str(recipe),'exec'),env);assert env['s']==new
 events=[json.loads(l)for l in(q/'events.jsonl').read_text().splitlines()];assert len(events)==2;failed=events[-1]['result'];assert failed['status']=='failed'and failed['reason']=='Lean exit 1'and type(failed['seconds'])in[int,float]and 0<failed['seconds']<240
 plan=json.loads((q/'plan.json').read_bytes());assert pin(q/'handwritten'/(module+'.lean'))['sha256']==plan['targets'][0]['source']['sha256'];assert (q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes();assert plan['pressure_limits']==fresh['pressure_limits']
 log=q/'runs'/('01-'+module)/'stdout.txt';z=[z for z in fresh['pins']if z['path'].endswith('stdout.txt')and ('transfer-source-typed-input-projection-20261011-'+n)in z['path']];assert len(z)==1 and pin(log)['bytes']==z[0]['bytes']and pin(log)['sha256']==z[0]['sha256'];diagnostics=[l for l in log.read_text().splitlines()if 'error:'in l or 'warning:'in l];assert diagnostics
 records.append(dict(attempt=n,source=pin(q/'handwritten'/(module+'.lean')),result=failed,recipe=pin(recipe),pure_repair_exact=True,all_definitions_contracts_unchanged=True,diagnostics=diagnostics,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True)))))
r=dict(status='PASSED',kind='Independent full source/model/contract and exact two-rejection history/maintained pure repair-chain review',source=pin(source),fresh_reports=6,definitions=3,theorems=3,rejected=records,scope='Installed configuration derives exact ordered all-slot nullifier word projection, mathematical Montgomery keys and canonical range. Inputs/wordOf are arbitrary typed selectors requiring actual pinned Rust iterator/accessor/field/library/byte/compiler/trace correspondence; this model configuration definition supplies no desired key vector/range premise. Full Transfer/native remains owned OPEN.',full_transfer='OPEN',native_execution='UNRUN')
out=D/'semantic-source-review01.json';assert not out.exists();out.write_text(json.dumps(r,indent=2)+'\n');kernel=D/'endpoint-audit-review01.json';k=json.loads(kernel.read_bytes());k['rejected']=records;k['semantic_scope']=r['scope'];k['precise_repair_review']=pin(out);kernel.write_text(json.dumps(k,indent=2)+'\n');print(json.dumps(dict(status='PASSED',reports=6,rejections=2,all_contracts_and_models_exact=True,pure_maintained_chain='EXACT')))
