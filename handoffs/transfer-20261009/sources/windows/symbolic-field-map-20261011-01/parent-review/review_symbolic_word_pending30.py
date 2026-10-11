"""Exact source generation and retained kernel-history review; no verifier."""
from pathlib import Path
import ast,re,json,hashlib,difflib,argparse
J=Path(__file__).resolve().parent
parser=argparse.ArgumentParser();parser.add_argument('label',choices=['symbolic-field-map','canonical-word-pending']);a=parser.parse_args()
D=J/('windows-'+a.label+'-review01');P=D/'packet01';M='TransferSymbolicFieldMap01' if a.label=='symbolic-field-map' else 'TransferCanonicalWordPending01';N=2 if a.label=='symbolic-field-map' else 8
S=P/'source/ShielddSecurity'/(M+'.lean');final=S.read_text()
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
old=[];records=[];W='TransferCanonicalWordPending01'
for number in ['01','02']:
 q=P/'unselected'/number;s=q/'handwritten'/(W+'.lean');before=s.read_text();assert before==(q/'project/ShielddSecurity'/(W+'.lean')).read_text();old.append(before)
 events=[json.loads(x) for x in(q/'events.jsonl').read_text().splitlines()];assert len(events)==2;result=events[-1]['result'];assert result['status']=='failed' and result['reason']=='Lean exit 1' and 0<result['seconds']<240
 assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes();assert json.loads((q/'plan.json').read_text())['pressure_limits']==json.loads((P/'qualified/plan.json').read_text())['pressure_limits']
 log=q/'runs'/('01-'+W)/'stdout.txt';assert '(kernel) excessive memory consumption detected' in log.read_text()
 records.append(dict(result=result,source=pin(s),log=pin(log),diagnostics=[l for l in log.read_text().splitlines() if 'error:' in l]))
exact_recipe(P/'unselected/01/prepare_recipe.py',raw(old[0],W,8),old[0]);exact_recipe(P/'unselected/02/prepare_recipe.py',old[0],old[1]);assert old[0].replace('_ = keys := List.map_id','_ = keys := List.map_id keys')==old[1]
if a.label=='symbolic-field-map':
 exact_recipe(P/'qualified/prepare_recipe.py',raw(final,M,N),final)
 scope='Polymorphic list projection and inverse follow from explicit pointwise equations. No concrete field inverse is assumed closed here; CanonicalWordPending supplies the pointwise equation from the previously proved constructed canonical scalar. Both original concrete kernel-memory failures and first list-argument error retained with original sources/logs/limits. Native implementation and full Transfer remain owned OPEN.'
else:
 exact_recipe(P/'qualified/prepare_recipe.py',old[1],final)
 contracts=lambda s:re.findall(r'^theorem ([\s\S]*?)(?=:=)',s,re.M)
 assert contracts(old[0])==contracts(old[1])==contracts(final)
 definitions=lambda s:re.findall(r'^(?:def|inductive) [\s\S]*?(?=^(?:def|inductive|theorem|set_option pp.all)|\Z)',s,re.M)
 assert definitions(old[0])==definitions(old[1])==definitions(final)
 records[-1]['exact_selected_delta']=''.join(difflib.unified_diff(old[1].splitlines(True),final.splitlines(True)))
 scope='Typed canonical raw Scalar words are constructed by the proved source LE/parser/choice/R2 decoder. Projection equals key modulo the pinned scalar field; canonical list and supported finite enum roundtrips and coherent bounded current pending restoration are derived. The symbolic pointwise premise is supplied by the proved constructor and input canonicality. Definitions/theorem contracts unchanged after two original kernel-memory failures; final proof instantiates the small symbolic map instead of unfolding concrete field terms. Seen membership remains an extensional list; actual private Rust Scalar/imbl/Any/Clone/Choice/CtOption/compiler/primitive/full native trace bindings and reachability of the supported domain remain owned OPEN.'
r=dict(status='PASSED_SOURCE_HISTORY',kind='Exact maintained handwritten/audit generation and complete original failures; semantic source review',source=pin(S),fresh_reports=N,rejected=records,scope=scope,full_transfer='OPEN',native_execution='UNRUN')
(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(label=a.label,status=r['status'],reports=N,failed_originals=len(records))))
