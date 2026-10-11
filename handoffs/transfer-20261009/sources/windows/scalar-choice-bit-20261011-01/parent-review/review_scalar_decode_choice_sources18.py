from pathlib import Path
import ast,json,re,hashlib
J=Path(__file__).parent
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def generate(recipe,source,count):
 nodes=ast.parse(recipe.read_text()).body;body=[]
 for n in nodes:
  if isinstance(n,ast.Expr)and isinstance(n.value,ast.Call)and isinstance(n.value.func,ast.Attribute)and n.value.func.attr=='mkdir'and 'handwritten'in ast.unparse(n):break
  if isinstance(n,ast.Assign)and all(isinstance(t,ast.Name)and t.id in ['source','names']for t in n.targets):body.append(n)
  elif isinstance(n,ast.For)and isinstance(n.iter,ast.Name)and n.iter.id=='names':body.append(n)
  elif isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='source':body.append(n)
 assert len(body)==4
 for n in body:
  for c in ast.walk(n):
   if isinstance(c,ast.Call):assert isinstance(c.func,ast.Attribute)and c.func.attr=='findall'and isinstance(c.func.value,ast.Name)and c.func.value.id=='re'
 env={'re':re};exec(compile(ast.Module(body=body,type_ignores=[]),'<pure-decoder-choice-generation>','exec'),env);assert env['source']==source.read_text()and len(env['names'])==count
for label,module,count in [('scalar-byte-decode','TransferScalarByteDecode01',7),('scalar-choice-bit','TransferScalarChoiceBit01',8)]:
 D=J/('windows-'+label+'-review01');P=D/'packet01';S=P/'source/ShielddSecurity'/(module+'.lean');recipe=P/'qualified'/('recipe_source.py'if label=='scalar-byte-decode'else'prepare_recipe.py');generate(recipe,S,count);extra={}
 if label=='scalar-byte-decode':
  q=P/'unrun-predecessor/01';assert not(q/'events.jsonl').exists();old=q/'handwritten'/(module+'.lean');assert old.read_bytes()==(q/'project/ShielddSecurity'/(module+'.lean')).read_bytes();generate(q/'prepare_recipe.py',old,7);a='TransferScalarMontgomeryValue01.fixed_four_word_typed_serializer_is_canonical words';b='TransferScalarLittleEndianBytes01.fixed_four_word_source_scalar_projection_is_canonical words';assert old.read_text().count(a)==1 and old.read_text().replace(a,b)==S.read_text();assert(q/'prepare_recipe.py').read_text().replace(a,b).replace('transfer-scalar-byte-decode-owned-floor-20261011-01','transfer-scalar-byte-decode-owned-floor-20261011-02')==recipe.read_text();extra=dict(unrun_predecessor=pin(q/'plan.json'),correct_reusable_theorem_only=True,contracts_unchanged=True)
 scope=('Typed UInt8 eight-byte LE chunks derive UInt64 bound and exact full-width packed integer reconstruction. Four-word borrow accepts iff exact32byte integer below field modulus; exact source serializer bytes pass. Native from_le_bytes/SBB/Choice/CtOption/Scalar invariant/R2 Montgomery conversion/compiler/full trace bindings owned OPEN'if label=='scalar-byte-decode'else'Finite UInt64 zero/all-ones borrow mask cast to UInt8 and AND1 yields exact0/1; canonical success/refusal bit derives parsed integer below/at-or-above field modulus, exact serializer bytes derive one. Actual native Choice/CtOption/R2 payload conversion/Scalar invariant/primitives/compiler/full trace bindings owned OPEN')
 r=dict(status='PASSED_SOURCE_HISTORY',kind='Independent exact pure maintained decoder/choice source regeneration and semantic contract review; prior kernel ancestry packet pending',source=pin(S),recipe=pin(recipe),review_helper=pin(Path(__file__)),fresh_reports=count,scope=scope,full_transfer='OPEN',native_execution='UNRUN',**extra);(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(label=label,status=r['status'],reports=count)))
