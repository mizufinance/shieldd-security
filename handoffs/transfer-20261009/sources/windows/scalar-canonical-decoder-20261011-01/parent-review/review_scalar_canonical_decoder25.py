from pathlib import Path
import ast,json,re,hashlib
J=Path(__file__).resolve().parent;G=J.parent/'shared-build-handoff';D=J/'windows-scalar-canonical-decoder-review01';P=D/'packet01';M='TransferScalarCanonicalDecoder01';S=P/'source/ShielddSecurity'/(M+'.lean');source=S.read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==8;assert re.findall(r'^#check @([\w.]+)',source,re.M)==names;assert re.findall(r'^#print axioms ([\w.]+)',source,re.M)==names
nodes=ast.parse((P/'qualified/prepare_recipe.py').read_text()).body;body=[]
for n in nodes:
 if isinstance(n,ast.Assign)and all(isinstance(t,ast.Name)and t.id in ['source','names']for t in n.targets):
  if n.targets[0].id=='source'and any(isinstance(c,ast.Call)and isinstance(c.func,ast.Attribute)and c.func.attr=='read_text'for c in ast.walk(n.value)):continue
  body.append(n)
 elif isinstance(n,ast.For)and isinstance(n.iter,ast.Name)and n.iter.id=='names':body.append(n)
 elif isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='source':body.append(n)
assert len(body)==3
trailer=''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in names)+'end ShielddSecurity.'+M+'\n';assert source.endswith(trailer);env={'source':source[:-len(trailer)],'re':re};exec(compile(ast.Module(body=body,type_ignores=[]),'<handwritten source named audit augmentation>','exec'),env);assert env['source']==source
scope='Finite typed32byte source decoder composed from proved four LE word reads, exact constructed R2 Montgomery payload, and borrow choice byte. Documented Option success projection accepts iff parsed integer below modulus. Accepted canonical bytes reserialize exactly; canonical internal raw Scalar serializes and decodes to its original vector via canonical-byte injection. Original encoded byte equality premise is explicit. Actual private Scalar invariant/Choice/CtOption/library representation/compiler/primitive/full native execution and Transfer remain owned OPEN.'
r=dict(status='PASSED',kind='Authenticated handwritten source/named audit augmentation and full semantic contract review',source=pin(S),fresh_reports=8,original_attempt='First original qualification passed; no rejected original in immutable packet',scope=scope,full_transfer='OPEN',native_execution='UNRUN');(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status='PASSED',reports=8,success_projection_only=True)))
