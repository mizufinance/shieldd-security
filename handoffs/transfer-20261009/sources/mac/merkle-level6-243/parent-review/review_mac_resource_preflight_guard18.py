from pathlib import Path
import ast,json,hashlib
J=Path(__file__).parent;W=J.parent
def pin(p):return dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
a=W/'mac-full-arithmetic45-execution220/maintained/guard.py';b=W/'mac-full-arithmetic45-execution223/maintained/guard.py'
ot=ast.parse(a.read_text());nt=ast.parse(b.read_text());of={x.name:ast.dump(x)for x in ot.body if isinstance(x,ast.FunctionDef)};nf={x.name:ast.dump(x)for x in nt.body if isinstance(x,ast.FunctionDef)}
assert set(nf)-set(of)=={'physical_preflight'}
assert [n for n in of if of[n]!=nf[n]]==['carried_check','execute']
oc=json.loads((a.parent.parent/'config01.json').read_text());nc=json.loads((b.parent.parent/'config01.json').read_text());assert oc['limits']==nc['limits']
assert of['bounds']==nf['bounds'] and of['fixed_check']==nf['fixed_check']
cn=next(n for n in nt.body if isinstance(n,ast.FunctionDef)and n.name=='carried_check');co=next(n for n in ot.body if isinstance(n,ast.FunctionDef)and n.name=='carried_check')
newtree=next(n for n in cn.body if isinstance(n,ast.FunctionDef)and n.name=='verify_tree');oldtree=next(n for n in co.body if isinstance(n,ast.FunctionDef)and n.name=='verify_tree')
assert len(newtree.body)==len(oldtree.body)+1
assert all(ast.dump(x)==ast.dump(y)for x,y in zip(newtree.body[:2],oldtree.body[:2]))
assert all(ast.dump(x)==ast.dump(y)for x,y in zip(newtree.body[4:],oldtree.body[3:]))
newtree.body=oldtree.body;assert ast.dump(cn)==ast.dump(co)
checks=0
for r in nc['charged_roots']:
 assert r.startswith('/')and '..'not in r.split('/')and '//'not in r and not r.endswith('/')
 for k in [r+'/child',r+'/child/x',r+'extra/x',r.rsplit('/',1)[0]+'/other',r]:
  assert k.startswith(r+'/')==(Path(k).is_relative_to(Path(r))and k!=r);checks+=1
s=b.read_text().replace('cancelled();physical_preflight(config)','cancelled();pre=bounds(config);launch_reserve(pre)')
s=s.replace('        if not cache.exists():\n            pre=bounds(config);launch_reserve(pre);initialize_overlay(config)','        if not cache.exists(): initialize_overlay(config)')
sf=next(n for n in ast.parse(s).body if isinstance(n,ast.FunctionDef)and n.name=='execute');assert ast.dump(sf)==of['execute']
checked=[]
for folder in ['mac-resource-preflight222-source01','mac-accounting-cache221-source02']:
 p=W/folder/'producer-manifest01.json';checked.append(pin(p))
 for z in json.loads(p.read_text()).values():assert pin(Path(z['path']))==z;checked.append(z)
report=dict(status='PASSED',kind='Independent deployed guard220-to223 AST/source, original producer pins and physical-limit review; no Lean or guard execution',old=pin(a),new=pin(b),checked=checked,physical_limits='UNCHANGED',all_other_functions='EXACT',historical_aliases='Exact unchanged bounds function; rejected221 shortcut undeployed',canonical_prefix_controls=checks,full_census='Exact full immediate-prelaunch and both postlaunch checks retained; two redundant early artifact scans replaced by physical RAM/disk admission; initialization reserve retained',review_harness_history='Initial root read-only draft referenced historical_aliases as top-level; it is nested in the unchanged bounds function. Corrected selector; no worker changes.',scope='Machine-safety optimization only; no theorem/native completion result',full_transfer='OPEN')
out=J/'mac-resource-preflight-guard-review18.json'
with out.open('x')as f:json.dump(report,f,indent=2);f.write('\n')
print(json.dumps(dict(status='PASSED',guard=pin(b)['sha256'],prefix_controls=checks)))
