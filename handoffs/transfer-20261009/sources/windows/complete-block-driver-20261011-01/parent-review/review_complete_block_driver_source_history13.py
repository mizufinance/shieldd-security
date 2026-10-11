from pathlib import Path
import ast,json,hashlib,re,difflib
J=Path(__file__).resolve().parent;D=J/'windows-complete-block-driver-review01';P=D/'packet01';M='TransferCompleteBlockDriver01';S=P/'source/ShielddSecurity'/(M+'.lean');final=S.read_text();q=P/'rejected-kernel/01';old=(q/'handwritten'/(M+'.lean')).read_text();assert old==(q/'project/ShielddSecurity'/(M+'.lean')).read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
upstream=J.parent/'shared-build-handoff/handoffs/transfer-20261009/sources/windows/absent-start-publication-20261011-01/absent-start-publication/source/ShielddSecurity/TransferAbsentStartPublication01.lean';e=next(x for x in json.loads((P/'context/owned-composition-review.json').read_text())['selected']if x['module']=='TransferAbsentStartPublication01');assert all(pin(upstream)[k]==e['source'][k]for k in ['bytes','sha256'])
def regenerate(p,expected):
 nodes=ast.parse(p.read_text()).body;cut=next(i for i,n in enumerate(nodes)if isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='mkdir');body=[];allowed={'source','names','oldSource','old','t','start','end','a','head','proof'}
 for n in nodes[:cut]:
  if isinstance(n,ast.Assign)and all(isinstance(t,(ast.Name,ast.Tuple))for t in n.targets)and all(x.id in allowed for t in n.targets for x in ast.walk(t)if isinstance(x,ast.Name)):
   if isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='read_text':assert n.targets[0].id=='old'
   else:body.append(n)
  elif isinstance(n,ast.For)and isinstance(n.iter,ast.Name)and n.iter.id=='names':body.append(n)
  elif isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='source':body.append(n)
 assert len(body)>=5
 for n in body:
  for c in ast.walk(n):
   if isinstance(c,ast.Call):assert isinstance(c.func,ast.Attribute)and ((isinstance(c.func.value,ast.Name)and c.func.value.id in {'re','source','oldSource','old','t','head'})or(isinstance(c.func.value,ast.Call)and c.func.attr=='replace')or(isinstance(c.func.value,ast.Subscript)and isinstance(c.func.value.value,ast.Name)and c.func.value.value.id=='old'and c.func.attr=='replace'))and c.func.attr in {'findall','index','replace','split','sub'}
 env={'old':upstream.read_text(),'re':re};exec(compile(ast.Module(body=body,type_ignores=[]),str(p),'exec'),env);assert env['source']==expected and len(env['names'])==2
regenerate(P/'qualified/recipe_source.py',final);regenerate(q/'prepare_recipe.py',old)
assert old.replace('refine ⟨final, ran, same.symm, ?_⟩','refine ⟨final, rfl, same.symm, ?_⟩')==final
repaired=(q/'prepare_recipe.py').read_text().replace('refine ⟨final, ran, same.symm, ?_⟩','refine ⟨final, rfl, same.symm, ?_⟩').replace('transfer-complete-block-driver-owned-floor-20261011-01','transfer-complete-block-driver-owned-floor-20261011-02');assert repaired==(P/'qualified/recipe_source.py').read_text()
events=[json.loads(l)for l in(q/'events.jsonl').read_text().splitlines()];assert len(events)==2;failed=events[-1]['result'];assert failed['status']=='failed'and failed['reason']=='Lean exit 1'and 0<failed['seconds']<240;prior=json.loads((q/'plan.json').read_text());fresh=json.loads((P/'qualified/plan.json').read_text());assert prior['pressure_limits']==fresh['pressure_limits']and(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes();diagnostics=[l for l in(q/'runs'/('01-'+M)/'stdout.txt').read_text().splitlines()if 'error:'in l or 'warning:'in l or 'sorryAx'in l];assert diagnostics
records=[dict(kind='Original failed case-split witness attempt, unselected',result=failed,source=pin(q/'handwritten'/(M+'.lean')),diagnostics=diagnostics,all_definitions_and_theorem_contracts_unchanged=True,proof_only_repair_exact=True,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),final.splitlines(True))))]
scope='Returned whole block model composes native-only walk from absent pending, assigns reached active host state, and executes installed tagged finalizer/publication. Success derives walk/reached-state witness and exact ordered mathematical inputs; caller walk/current-state equations removed. None has no failure-prefix or rollback claim. Actual Rust loop/cache/Host ownership/selectors/component trace/library/snapshot/OS correspondence remains owned OPEN. Predecessor native finalization order gap retained'
r=dict(status='PASSED',kind='Independent pure exact original source generation, repair and complete failed-attempt review',source=pin(S),upstream=pin(upstream),fresh_reports=2,rejected=records,scope=scope,full_transfer='OPEN',native_execution='UNRUN');out=D/'semantic-source-review01.json';out.write_text(json.dumps(r,indent=2)+'\n');p=D/'endpoint-audit-review01.json';k=json.loads(p.read_text());k.update(rejected=records,semantic_scope=scope,precise_repair_review=pin(out));p.write_text(json.dumps(k,indent=2)+'\n');print(json.dumps(dict(status='PASSED',reports=2,failed_originals=1)))
