"""Exact typed-object/source-driver semantic and original history review; no verifier."""
from pathlib import Path
import ast,re,json,hashlib,difflib,argparse
J=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument("label",choices=["word-object-codec","word-source-driver"]);a=parser.parse_args()
D=J/("windows-"+a.label+"-review01");P=D/"packet01";M="TransferWordObjectCodec01" if a.label=="word-object-codec" else "TransferWordSourceDriver01";N=8 if a.label=="word-object-codec" else 5
S=P/"source/ShielddSecurity"/(M+".lean");final=S.read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())

def audit_tail(s,module,count):
 names=re.findall(r'^(?:inductive|def|theorem) ([A-Za-z0-9_]+)',s,re.M);assert len(names)==count
 return ''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in names)+'end ShielddSecurity.'+module+'\n'

def raw(s,module,count):
 t=audit_tail(s,module,count);assert s.endswith(t);return s[:-len(t)]+'end ShielddSecurity.'+module+'\n'

def exact_recipe(p,seed,expected):
 env={'re':re};seen=False
 for n in ast.parse(p.read_text()).body:
  if isinstance(n,ast.Assign) and all(isinstance(t,ast.Name) and t.id in {'source','names','start','end'} for t in n.targets):
   if not seen:
    if n.targets[0].id!='source':continue
    assert any(isinstance(c,ast.Call) and isinstance(c.func,ast.Attribute) and c.func.attr=='read_text' for c in ast.walk(n.value));env['source']=seed;seen=True
    if isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute) and n.value.func.attr=='removesuffix':env['source']=seed.removesuffix(ast.literal_eval(n.value.args[0]))
    continue
   for c in ast.walk(n):
    if isinstance(c,ast.Call):assert isinstance(c.func,ast.Attribute) and c.func.attr in {'replace','removesuffix','findall','index'} and isinstance(c.func.value,ast.Name) and c.func.value.id in {'source','re'}
   exec(compile(ast.Module(body=[n],type_ignores=[]),str(p),'exec'),env)
  elif seen and isinstance(n,ast.For) and isinstance(n.iter,ast.Name) and n.iter.id=='names':
   assert len(n.body)==1 and isinstance(n.body[0],ast.AugAssign) and isinstance(n.body[0].target,ast.Name) and n.body[0].target.id=='source';exec(compile(ast.Module(body=[n],type_ignores=[]),str(p),'exec'),env)
  elif seen and isinstance(n,ast.AugAssign) and isinstance(n.target,ast.Name) and n.target.id=='source':exec(compile(ast.Module(body=[n],type_ignores=[]),str(p),'exec'),env)
  elif seen and isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Attribute) and n.value.func.attr=='write_text' and isinstance(n.value.args[0],ast.Name) and n.value.args[0].id=='source':break
 assert seen and env['source']==expected

records=[]
if a.label=='word-object-codec':
 exact_recipe(P/'qualified/prepare_recipe.py',raw(final,M,N),final)
 assert not(P/'unselected').exists()
 scope='Concrete heterogeneous typed pending-word tag derives supported enum identity/restored observations and canonical bounded sealed getter from the constructed field codec. All getter theorems apply to encoded pending values. decodeNative on the other-object tag intentionally totalizes to empty in this projection model; this does not represent the actual wrong-type panic and is not accepted as a full native getter. The worker is separately refining checked getter branches. Extended ghost state, real private Scalar/Any/downcast/Clone/imbl/compiler/primitives/ownership and full native trace/full Transfer remain owned OPEN.'
else:
 G=J.parent/'shared-build-handoff';seedpath=G/'handoffs/transfer-20261009/sources/windows/source-ordered-driver-20261011-01/source-ordered-driver/source/ShielddSecurity/TransferSourceOrderedDriver01.lean';seed=seedpath.read_text();recipe=P/'unselected/02/prepare_recipe.py';env={};seen=False
 for n in ast.parse(recipe.read_text()).body:
  if isinstance(n,ast.Assign) and all(isinstance(t,ast.Name) and t.id in {'source','scope','helper','start','end','at'}for t in n.targets):
   if n.targets[0].id=='scope':assert not any(isinstance(x,ast.Call)for x in ast.walk(n.value));exec(compile(ast.Module(body=[n],type_ignores=[]),str(recipe),'exec'),env);continue
   if not seen:
    if n.targets[0].id!='source':continue
    assert any(isinstance(c,ast.Call)and isinstance(c.func,ast.Attribute)and c.func.attr=='read_text'for c in ast.walk(n.value));env['source']=seed;seen=True;continue
   for c in ast.walk(n):
    if isinstance(c,ast.Call):assert isinstance(c.func,ast.Attribute)and c.func.attr in {'replace','index'} and (isinstance(c.func.value,ast.Name)and c.func.value.id=='source' or isinstance(c.func.value,ast.Call))
   exec(compile(ast.Module(body=[n],type_ignores=[]),str(recipe),'exec'),env)
  elif seen and isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='write_text'and isinstance(n.value.args[0],ast.Name)and n.value.args[0].id=='source':break
 assert seen and env['source']==final
 q=P/'unselected/01';old=(q/'handwritten'/(M+'.lean')).read_text();assert not(q/'events.jsonl').exists()and not(q/'plan.json').exists()
 split='set_option pp.all true in\n#check @';assert old.split(split)[0]==final.split(split)[0];assert sorted(re.findall(r'^#check @([^\n]+)',old,re.M))==sorted(re.findall(r'^#check @([^\n]+)',final,re.M));records.append(dict(kind='Unrun report-order/import setup; no verifier attempt',source=pin(q/'handwritten'/(M+'.lean')),exact_delta=''.join(difflib.unified_diff(old.splitlines(True),final.splitlines(True)))))
 q=P/'unselected/02';assert(q/'handwritten'/(M+'.lean')).read_text()==final==(q/'project/ShielddSecurity'/(M+'.lean')).read_text();events=[json.loads(x)for x in(q/'events.jsonl').read_text().splitlines()];assert len(events)==2;result=events[-1]['result'];assert result['status']=='failed'and result['reason']=='Physical memory pressure'and 0<result['seconds']<240;assert not list(q.rglob('stdout.txt'))
 assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes();assert json.loads((q/'plan.json').read_text())['pressure_limits']==json.loads((P/'qualified/plan.json').read_text())['pressure_limits'];records.append(dict(kind='Original physical pressure refusal with no compiler log',result=result,source=pin(q/'handwritten'/(M+'.lean')),events=pin(q/'events.jsonl'),source_and_guards_unchanged=True))
 qr=ast.parse((P/'qualified/prepare_recipe.py').read_text());copies=[n for n in ast.walk(qr)if isinstance(n,ast.Call)and isinstance(n.func,ast.Attribute)and n.func.attr=='copyfile'];assert len(copies)==1
 scope='Successful whole returned modeled driver derives the actual walk, exact ordered mathematical source inputs, supported canonical sealed typed-word object, frozen accepted insertions/application root/Ready/Idle/physical commit boundary. Returned outcome and root success supply operational premises; no desired final object/getter/codec roundtrip/domain/injection premise is supplied. Exact construction from independently accepted source-ordered driver verified; unrun audit-order setup and original physical pressure refusal retained, fresh source unchanged. This still uses the totalized projection getter and extended ghost carrier; wrong-type panic and real private Scalar/Any/imbl/compiler/primitives/callee/value/ownership/OS/full native trace bindings and full Transfer remain owned OPEN.'
r=dict(status='PASSED_SOURCE_HISTORY',kind='Exact maintained source generation, original setup/pressure history and semantic review',source=pin(S),fresh_reports=N,rejected=records,scope=scope,full_transfer='OPEN',native_execution='UNRUN');(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(label=a.label,status=r['status'],reports=N,history=len(records))))
