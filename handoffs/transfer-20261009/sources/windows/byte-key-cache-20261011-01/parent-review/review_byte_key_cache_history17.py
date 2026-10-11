from pathlib import Path
import ast,json,re,hashlib,difflib
J=Path(__file__).parent;D=J/'windows-byte-key-cache-review01';P=D/'packet01';M='TransferByteKeyCache01'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def regenerate(recipe,source):
 nodes=ast.parse(recipe.read_text()).body;body=[]
 for n in nodes:
  if isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='mkdir':break
  if isinstance(n,ast.Assign)and all(isinstance(t,ast.Name)and t.id in ['source','names']for t in n.targets):body.append(n)
  elif isinstance(n,ast.For)and isinstance(n.iter,ast.Name)and n.iter.id=='names':body.append(n)
  elif isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='source':body.append(n)
 assert len(body)==4
 for n in body:
  for c in ast.walk(n):
   if isinstance(c,ast.Call):assert isinstance(c.func,ast.Attribute)and c.func.attr=='findall'and isinstance(c.func.value,ast.Name)and c.func.value.id=='re'
 env={'re':re};exec(compile(ast.Module(body=body,type_ignores=[]),'<pure-byte-key-literal-generation>','exec'),env);assert env['source']==source.read_text()and len(env['names'])==7
S=P/'source/ShielddSecurity'/(M+'.lean');regenerate(P/'qualified/recipe_source.py',S);old=[];failed=[]
for n in ['01','02','03']:
 q=P/'unselected'/n;s=q/'handwritten'/(M+'.lean');assert s.read_bytes()==(q/'project/ShielddSecurity'/(M+'.lean')).read_bytes();regenerate(q/('prepare_recipe.py'if n=='01'else'recipe_source.py'),s);old.append(s.read_text());assert(q/'execute_bounded.py').read_bytes()==(P/'qualified/execute_bounded.py').read_bytes();assert json.loads((q/'plan.json').read_text())['pressure_limits']==json.loads((P/'qualified/plan.json').read_text())['pressure_limits'];e=q/'events.jsonl'
 if n=='03':assert not e.exists();continue
 events=[json.loads(v)for v in e.read_text().splitlines()];assert len(events)==2;result=events[-1]['result'];assert result['status']=='failed'and result['reason']==('Lean exit 1'if n=='01'else'Physical memory pressure')and 0<result['seconds']<240;failed.append(dict(result=result,source=pin(s),stdout=pin(q/'runs'/('01-'+M)/'stdout.txt')))
before='⟨TransferInjectiveKeyPublication01.keyCode_is_injective, congrArg keyCode⟩';after='⟨fun same => TransferInjectiveKeyPublication01.keyCode_is_injective same, fun same => congrArg keyCode same⟩';assert old[0].replace(before,after)==old[1]==old[2]
recipe=ast.parse((P/'qualified/prepare_recipe.py').read_text());replacement=next(n.value for n in recipe.body if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id=='replacements'for t in n.targets));repairs=ast.literal_eval(replacement);assert set(repairs)=={'fun same => TransferInjectiveKeyPublication01.keyCode_is_injective same','  simp only [writeAtBytes, putObject, putByteWrite, encoded_key_equality_iff_exact_byte_key_equality]'};final=old[2]
for a,b in repairs.items():assert final.count(a)==1;final=final.replace(a,b)
assert final==S.read_text();original_recipe=(P/'unselected/03/recipe_source.py').read_text().replace('transfer-byte-key-cache-owned-floor-20261011-03','transfer-byte-key-cache-owned-floor-20261011-04')
for a,b in repairs.items():assert original_recipe.count(a)==1;original_recipe=original_recipe.replace(a,b)
assert original_recipe==(P/'qualified/recipe_source.py').read_text()
r=dict(status='PASSED_SOURCE_HISTORY',kind='Independent exact maintained generation and all retained failed/unrun source repairs; kernel ancestry review pending reversed-order dependency',source=pin(S),recipe=pin(P/'qualified/recipe_source.py'),review_helper=pin(Path(__file__)),fresh_reports=7,failed_originals=failed,unrun_original=pin(P/'unselected/03/plan.json'),all_definitions_contracts_unchanged=True,exact_delta=''.join(difflib.unified_diff(old[0].splitlines(True),final.splitlines(True))),scope='Exact byte-key observation of symbolic Nat-key cache via derived global keyCode injection. Put/deletion tombstone, no-write overlay and latest-write merge preserved. Byte key renaming model; actual Rust String/UTF8/hash-map/Any/Clone/ownership/compiler/cache/full trace bindings owned OPEN',full_transfer='OPEN',native_execution='UNRUN');(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status=r['status'],reports=7,failed=2,unrun=1)))
