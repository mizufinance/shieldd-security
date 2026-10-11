"""Exact original handwritten bases, audit augmentation and source repair deltas; no Lean."""
from pathlib import Path
import ast,re,json,hashlib,difflib
J=Path(__file__).resolve().parent

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
  if isinstance(n,ast.Assign)and all(isinstance(t,ast.Name)and t.id in {'source','needle','names','oldproof','newproof'}for t in n.targets):
   if not seen:
    if n.targets[0].id!='source':continue
    assert any(isinstance(c,ast.Call)and isinstance(c.func,ast.Attribute)and c.func.attr=='read_text'for c in ast.walk(n.value));env['source']=seed;seen=True
    if isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='removesuffix':env['source']=seed.removesuffix(ast.literal_eval(n.value.args[0]))
    continue
   for c in ast.walk(n):
    if isinstance(c,ast.Call):assert isinstance(c.func,ast.Attribute)and c.func.attr in {'replace','removesuffix','findall'} and (isinstance(c.func.value,ast.Name)and c.func.value.id in {'source','re'}or isinstance(c.func.value,ast.Call))
   exec(compile(ast.Module(body=[n],type_ignores=[]),str(p),'exec'),env)
  elif seen and isinstance(n,ast.For)and isinstance(n.iter,ast.Name)and n.iter.id=='names':
   assert len(n.body)==1 and isinstance(n.body[0],ast.AugAssign)and isinstance(n.body[0].target,ast.Name)and n.body[0].target.id=='source';exec(compile(ast.Module(body=[n],type_ignores=[]),str(p),'exec'),env)
  elif seen and isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='source':exec(compile(ast.Module(body=[n],type_ignores=[]),str(p),'exec'),env)
  elif seen and isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='write_text'and isinstance(n.value.args[0],ast.Name)and n.value.args[0].id=='source':break
 assert seen and env['source']==expected
 assert len(re.findall(r'^#check @',expected,re.M))==count

scopes={
'scalar-wide-round':'Four-limb source-shaped MAC round proves low-word cancellation, exact shifted integer conservation, and width. Upper ADC consumes pending and MAC carry; new carry retains radix^4 weight. No desired cancellation/output premise. Actual Rust primitive/compiler/full execution binding remains owned OPEN.',
'scalar-wide-walk':'Source-shaped wide round recurrence derives four-word final width, radix-powered modular value and final less-than-two-modulus bound from explicit input width/range. No desired output premise. Actual Rust primitive/compiler/full execution binding remains owned OPEN.',
'scalar-wide-reduction':'Eight-word source-shaped four-round reduction derives zero final discarded carry, four-limb width, canonical result and Montgomery modular relation from explicit input bound. Canonical right operand derives full schoolbook-product input bound; exact borrowed-sub/masked-addback normalization used. Actual private Scalar invariant, primitive/compiler/full native execution binding remains owned OPEN.'}
for label,module,count in [('scalar-wide-round','TransferScalarWideRound01',6),('scalar-wide-walk','TransferScalarWideWalk01',7),('scalar-wide-reduction','TransferScalarWideReduction01',8)]:
 D=J/('windows-'+label+'-review01');P=D/'packet01';S=P/'source/ShielddSecurity'/(module+'.lean');final=S.read_text();olds=[];records=[]
 for q in sorted((P/'unselected').iterdir()):
  source=q/'handwritten'/(module+'.lean');old=source.read_text();olds.append(old);project=q/'project/ShielddSecurity'/(module+'.lean')
  if project.exists():assert project.read_text()==old
  ev=q/'events.jsonl'
  if ev.exists():
   events=[json.loads(l)for l in ev.read_text().splitlines()];assert len(events)==2;r=events[-1]['result'];assert r['status']=='failed'and r['reason']in {'Lean exit 1','Physical memory pressure'}and 0<r['seconds']<240
   assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes();assert json.loads((q/'plan.json').read_text())['pressure_limits']==json.loads((P/'qualified/plan.json').read_text())['pressure_limits']
   diagnostics=[l for l in(q/'runs'/('01-'+module)/'stdout.txt').read_text().splitlines()if 'error:'in l or 'sorryAx'in l];records.append(dict(kind='Original unselected failed attempt',result=r,source=pin(source),diagnostics=diagnostics,exact_delta=''.join(difflib.unified_diff(old.splitlines(True),final.splitlines(True)))))
  else:records.append(dict(kind='Original handwritten setup source UNRUN, no kernel credit',source=pin(source),exact_delta=''.join(difflib.unified_diff(old.splitlines(True),final.splitlines(True)))))
 if label=='scalar-wide-round':
  exact_recipe(P/'unselected/02/recipe_source.py',olds[0],olds[1],module,count);exact_recipe(P/'unselected/03/prepare_recipe.py',olds[1],olds[2],module,count);seed=olds[2]
 else:
  exact_recipe(P/'unselected/01/prepare_recipe.py',raw(olds[0],module,count),olds[0],module,count);seed=olds[0]
 exact_recipe(P/'qualified/prepare_recipe.py',seed,final,module,count)
 # Fresh source definitions are identical; walk also repairs coefficient grouping in a failed theorem expression.
 definitions=lambda s:re.findall(r'^def [\s\S]*?(?=\n(?:def|theorem) )',s,re.M)
 assert definitions(olds[0])==definitions(final)
 extra=dict(definitions_unchanged=True,accepted_full_type_authoritative=True,repair_classification='Explicit definitional reduction/typed bounds/distributivity only'if label!='scalar-wide-walk'else'Failed source coefficient grouping corrected in theorem expression and proof, plus list rewrite/distributivity; no claim of a qualified prior theorem')
 r=dict(status='PASSED_SOURCE_HISTORY',kind='Authenticated original handwritten bases, exact named audit augmentation and pure repair replay; kernel ancestry pending product',source=pin(S),fresh_reports=count,review_helper=pin(Path(__file__)),rejected=records,scope=scopes[label],full_transfer='OPEN',native_execution='UNRUN',**extra);(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(label=label,status=r['status'],reports=count,prior_attempts=len(records))))
