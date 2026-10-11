from pathlib import Path
import json,hashlib,ast,re,difflib,argparse
J=Path(__file__).parent;p=argparse.ArgumentParser();p.add_argument('label',choices=['known-finalizer-publication','installed-source-publication']);a=p.parse_args();D=J/('windows-'+a.label+'-review01');P=D/'packet01';module='TransferKnownFinalizerPublication01'if a.label=='known-finalizer-publication'else'TransferInstalledSourcePublication01';S=P/'source/ShielddSecurity'/(module+'.lean');final=S.read_text();recipe=P/'qualified/recipe_source.py'
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def regenerate(p,expected):
 nodes=ast.parse(p.read_text()).body;cut=next(i for i,n in enumerate(nodes)if isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='mkdir');nodes=nodes[:cut];body=[]
 upstream=(J.parent/'shared-build-handoff/handoffs/transfer-20261009/sources/windows/typed-scalar-publication-20261011-01/typed-scalar-publication/source/ShielddSecurity/TransferTypedScalarPublication01.lean')if a.label=='known-finalizer-publication'else(J/'windows-known-finalizer-publication-review01/packet01/source/ShielddSecurity/TransferKnownFinalizerPublication01.lean')
 upstream_module='TransferTypedScalarPublication01'if a.label=='known-finalizer-publication'else'TransferKnownFinalizerPublication01'
 owned=json.loads((P/'context/owned-composition-review.json').read_text());entry=next(e for e in owned['selected']if e['module']==upstream_module);assert pin(upstream)['bytes']==entry['source']['bytes']and pin(upstream)['sha256']==entry['source']['sha256']
 for n in nodes:
  if isinstance(n,ast.Assign)and all(isinstance(t,(ast.Name,ast.Tuple))for t in n.targets)and all(x.id in {'source','names','t','start','end','head','proof'}for t in n.targets for x in ast.walk(t)if isinstance(x,ast.Name)):
   if isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='read_text':assert len(n.targets)==1 and n.targets[0].id=='t'
   else:body.append(n)
  elif isinstance(n,ast.For)and isinstance(n.iter,ast.Name)and n.iter.id=='names':body.append(n)
  elif isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='source':body.append(n)
 assert len(body)>=10 and isinstance(body[0].value,ast.Constant)
 assert all(isinstance(c.func,ast.Attribute)and isinstance(c.func.value,ast.Name)and c.func.value.id in {'re','t','head'}and c.func.attr in {'findall','index','replace','split','sub'}for n in body for c in ast.walk(n)if isinstance(c,ast.Call))
 env={'re':re,'t':upstream.read_text()};exec(compile(ast.Module(body=body,type_ignores=[]),str(p),'exec'),env);assert env['source']==expected and len(env['names'])==7
regenerate(recipe,final)
headers=lambda s:[m.group(0).split(' := by')[0].split(' :=\n')[0]for m in re.finditer(r'(?m)^theorem [\s\S]*?(?=^theorem |^def |^set_option pp.all|\Z)',s)]
q=P/'rejected-kernel'/('02'if a.label=='known-finalizer-publication'else'01');old=(q/'handwritten'/(module+'.lean')).read_text();assert old==(q/'project/ShielddSecurity'/(module+'.lean')).read_text();assert headers(old)==headers(final)
fix=P/'qualified/prepare_recipe.py';nodes=ast.parse(fix.read_text()).body;selected=[]
for i,n in enumerate(nodes):
 if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='a'for t in n.targets)and isinstance(n.value,ast.Constant)and isinstance(n.value.value,str)and n.value.value in old:
  if isinstance(nodes[i+1],ast.Assign):segment=nodes[i:i+4];assert isinstance(segment[1].value,ast.Constant)and isinstance(segment[2],ast.Assert);expected=ast.parse('s.replace(a,b)',mode='eval').body
  else:segment=nodes[i:i+3];assert isinstance(segment[1],ast.Assert);expected=ast.parse('s.replace(a,'+repr(segment[2].value.args[1].value)+')',mode='eval').body
  assert ast.dump(segment[-1].value)==ast.dump(expected);selected.extend(segment)
assert len(selected)==(3 if a.label=='known-finalizer-publication' else 4)
env={'s':old};exec(compile(ast.Module(body=selected,type_ignores=[]),str(fix),'exec'),env);assert env['s']==final
if a.label=='known-finalizer-publication':assert re.sub(r'\s+','',old)==re.sub(r'\s+','',final)
else:
 assert old.replace('nonempty := by\n    change ((inputs request.base.action).map (fun input => scalarKey (wordOf input))).isEmpty = false\n    rw [List.isEmpty_map]\n    exact request.sourceNonempty}', 'nonempty := (List.isEmpty_map (l := inputs request.base.action) (f := fun input => scalarKey (wordOf input))).trans request.sourceNonempty}')==final
fresh=json.loads((P/'qualified/plan.json').read_text());prior=json.loads((q/'plan.json').read_text());events=[json.loads(l)for l in(q/'events.jsonl').read_text().splitlines()];assert len(events)==2;failed=events[-1]['result'];assert failed['status']=='failed'and failed['reason']=='Lean exit 1'and 0<failed['seconds']<240
assert prior['pressure_limits']==fresh['pressure_limits']and(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes()
log=q/'runs'/('01-'+module)/'stdout.txt';diagnostics=[l for l in log.read_text().splitlines()if 'error:'in l or 'warning:'in l or 'sorryAx'in l];assert diagnostics
records=[dict(kind='Rejected original kernel attempt, not semantic control evidence',result=failed,source=pin(q/'handwritten'/(module+'.lean')),diagnostics=diagnostics,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),final.splitlines(True))),all_theorem_contracts_unchanged=True,pure_maintained_repair_exact=True)]
if a.label=='known-finalizer-publication':
 setup=P/'rejected-setup/01';assert(setup/'handwritten'/(module+'.lean')).read_text()==old;regenerate(setup/'prepare_recipe.py',old);records.insert(0,dict(kind='Rejected original setup before plan/kernel, no verification result',recipe=pin(setup/'prepare_recipe.py'),source=pin(setup/'handwritten'/(module+'.lean')),source_same_as_original_failed_kernel=True,scope='Original preparation multiplicity refusal reported; full original source retained. No plan/events/kernel run claimed.'))
scope=('Concrete installed six-key object mutation finalizer derives pending retention and propagates exact typed global vector/publication/recovery under modeled success; sourceProjection still supplied. Effects trace completeness/order/value/native execution remains owned OPEN.'if a.label=='known-finalizer-publication'else'Installed typed requests derive every sourceProjection and ordered word vector; known finalizer derives retained pending object and publication/recovery under modeled success. Actual action/word selectors/nonempty/codec/getter/key injection and full native trace/runtime correspondence remains owned OPEN.')
r=dict(status='PASSED',kind='Independent exact pure maintained source/repair generation and full failed history/model/contract review',source=pin(S),recipe=pin(recipe),fresh_reports=7,rejected=records,scope=scope,full_transfer='OPEN',native_execution='UNRUN')
out=D/'semantic-source-review01.json'
with out.open('x')as f:json.dump(r,f,indent=2);f.write('\n')
kernel=D/'endpoint-audit-review01.json'
if kernel.exists():
 k=json.loads(kernel.read_text());k['rejected']=records;k['semantic_scope']=scope;k['precise_repair_review']=pin(out);kernel.write_text(json.dumps(k,indent=2)+'\n')
print(json.dumps(dict(status='PASSED',module=module,reports=7,rejections=len(records),pure_source_and_repair='EXACT')))
