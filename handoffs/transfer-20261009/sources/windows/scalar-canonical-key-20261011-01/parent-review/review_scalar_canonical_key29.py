from pathlib import Path
import ast,re,json,hashlib,difflib
J=Path(__file__).resolve().parent;D=J/'windows-scalar-canonical-key-review01';P=D/'packet01';M='TransferScalarCanonicalKey01';S=P/'source/ShielddSecurity'/(M+'.lean');final=S.read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())

def tail(source,module,count):
 names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==count
 return ''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in names)+'end ShielddSecurity.'+module+'\n'

def raw(source,module,count):
 t=tail(source,module,count);assert source.endswith(t);return source[:-len(t)]+'end ShielddSecurity.'+module+'\n'

def exact_recipe(p,seed,expected,module,count):
 nodes=ast.parse(p.read_text()).body;env={'re':re};seen=False
 for n in nodes:
  if isinstance(n,ast.Assign)and all(isinstance(t,ast.Name)and t.id in {'source','needle','names','oldproof','newproof','start','end'}for t in n.targets):
   if not seen:
    if n.targets[0].id!='source':continue
    assert any(isinstance(c,ast.Call)and isinstance(c.func,ast.Attribute)and c.func.attr=='read_text'for c in ast.walk(n.value));env['source']=seed;seen=True
    if isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='removesuffix':env['source']=seed.removesuffix(ast.literal_eval(n.value.args[0]))
    continue
   for c in ast.walk(n):
    if isinstance(c,ast.Call):assert isinstance(c.func,ast.Attribute)and c.func.attr in {'replace','removesuffix','findall','index'} and (isinstance(c.func.value,ast.Name)and c.func.value.id in {'source','re'}or isinstance(c.func.value,ast.Call))
   exec(compile(ast.Module(body=[n],type_ignores=[]),str(p),'exec'),env)
  elif seen and isinstance(n,ast.For)and isinstance(n.iter,ast.Name)and n.iter.id=='names':
   assert len(n.body)==1 and isinstance(n.body[0],ast.AugAssign)and isinstance(n.body[0].target,ast.Name)and n.body[0].target.id=='source';exec(compile(ast.Module(body=[n],type_ignores=[]),str(p),'exec'),env)
  elif seen and isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='source':exec(compile(ast.Module(body=[n],type_ignores=[]),str(p),'exec'),env)
  elif seen and isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='write_text'and isinstance(n.value.args[0],ast.Name)and n.value.args[0].id=='source':break
 assert seen and env['source']==expected
 assert len(re.findall(r'^#check @',expected,re.M))==count
old=[];records=[]
for number in ['01','02']:
 q=P/'unselected'/number;s=q/'handwritten'/(M+'.lean');before=s.read_text();assert before==(q/'project/ShielddSecurity'/(M+'.lean')).read_text();old.append(before);events=[json.loads(x)for x in(q/'events.jsonl').read_text().splitlines()];assert len(events)==2;r=events[-1]['result'];assert r['status']=='failed'and r['reason']=='Lean exit 1'and 0<r['seconds']<240;assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes();assert json.loads((q/'plan.json').read_text())['pressure_limits']==json.loads((P/'qualified/plan.json').read_text())['pressure_limits'];diagnostics=[l for l in(q/'runs'/('01-'+M)/'stdout.txt').read_text().splitlines()if 'error:'in l];assert diagnostics;records.append(dict(kind='Original failed elaboration attempt, unchanged limits',result=r,source=pin(s),diagnostics=diagnostics,exact_delta=''.join(difflib.unified_diff(before.splitlines(True),final.splitlines(True)))))
exact_recipe(P/'unselected/01/prepare_recipe.py',raw(old[0],M,8),old[0],M,8);exact_recipe(P/'unselected/02/prepare_recipe.py',old[0],old[1],M,8);exact_recipe(P/'qualified/prepare_recipe.py',old[1],final,M,8)
needle='namespace ShielddSecurity.TransferScalarCanonicalKey01\n';assert old[1].replace(needle,needle+'attribute [local irreducible] TransferScalarLittleEndianBytes01.scalarKey\n')==final
contracts=lambda s:re.findall(r'^theorem ([\s\S]*?)(?=:=)',s,re.M);assert contracts(old[0])==contracts(old[1])==contracts(final)
scope='Constructs every mathematical Fin field-modulus key as exact typed32byte LE encoding then modeled canonical R2 decoder payload. Projection, source decoder success, exact bytes, global inverse over canonical raw four-word vectors and key equality injection are derived. Two original heartbeat/elaboration failures retained; proof equality chain repaired and scalarKey local irreducibility changes elaboration only. Mathematical theorem contracts/definitions unchanged. Actual private Rust Scalar invariant/type/compiler/primitives/Choice/CtOption/collections and full native execution/Transfer remain owned OPEN.'
r=dict(status='PASSED',kind='Exact authenticated handwritten/audit generation, complete original failed sources/repairs and semantic review',source=pin(S),fresh_reports=8,rejected=records,contracts_unchanged=True,local_irreducibility_only=True,scope=scope,full_transfer='OPEN',native_execution='UNRUN');(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status='PASSED',reports=8,failed_originals=2)))
