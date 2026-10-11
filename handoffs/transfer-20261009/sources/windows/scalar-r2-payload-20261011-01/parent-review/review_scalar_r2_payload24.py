from pathlib import Path
import ast,json,re,hashlib
J=Path(__file__).resolve().parent;G=J.parent/'shared-build-handoff';D=J/'windows-scalar-r2-payload-review01';P=D/'packet01';M='TransferScalarR2Payload01';S=P/'source/ShielddSecurity'/(M+'.lean');source=S.read_text()
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
names=re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)',source,re.M);assert len(names)==7;assert re.findall(r'^#check @([\w.]+)',source,re.M)==names;assert re.findall(r'^#print axioms ([\w.]+)',source,re.M)==names
nodes=ast.parse((P/'qualified/prepare_recipe.py').read_text()).body;body=[]
for n in nodes:
 if isinstance(n,ast.Assign)and all(isinstance(t,ast.Name)and t.id in ['source','names']for t in n.targets):
  if n.targets[0].id=='source'and any(isinstance(c,ast.Call)and isinstance(c.func,ast.Attribute)and c.func.attr=='read_text'for c in ast.walk(n.value)):continue
  body.append(n)
 elif isinstance(n,ast.For)and isinstance(n.iter,ast.Name)and n.iter.id=='names':body.append(n)
 elif isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='source':body.append(n)
assert len(body)==3
trailer=''.join('set_option pp.all true in\n#check @'+n+'\n#print axioms '+n+'\n'for n in names)+'end ShielddSecurity.'+M+'\n';assert source.endswith(trailer);env={'source':source[:-len(trailer)],'re':re};exec(compile(ast.Module(body=body,type_ignores=[]),'<handwritten source named audit augmentation>','exec'),env);assert env['source']==source
library=G/'handoffs/transfer-20261009/sources/windows/bounded-native-codec-20261011-01/bounded-native-codec/qualified/context/runtime-library/bls12_381-0.8.0-scalar.rs';data=library.read_bytes();assert len(data)==36086 and hashlib.sha256(data).hexdigest()=='986f81e7fcb783a668bc4ab55721b22d497c5860cd7136e3cc600d2d9c321475';text=data.decode();match=re.search(r'const R2: Scalar = Scalar\(\[(.*?)\]\);',text,re.S);assert match;words=[int(w.replace('_',''),16)for w in re.findall(r'0x[0-9a-f_]+',match[1])];assert words==[0xc999e990f3f29c6d,0x2b6cedcb87925c23,0x05d314967254398f,0x0748d9d99f59ff11];a=text.index('    pub fn from_bytes(');b=text.index('    /// Converts',a);native=text[a:b];shape=json.loads((P/'context/r2-decoder-payload-shape.json').read_text());assert shape['decoder_body']==native;assert shape['library']['sha256']==hashlib.sha256(data).hexdigest();assert 'tmp *= &R2;'in native and 'CtOption::new(tmp, Choice::from(is_some))'in native;assert [int(w,16)for w in re.findall(r'0x[0-9a-f]+',source)]==words and shape['words']==words and shape['r2_definition']==match[0]
scope='Exact pinned R2 constant, derived source schoolbook/wide-reduction output constructs canonical four-word decoder payload for every input raw vector. Its raw Montgomery value and serializer value modulo the field modulus are derived, exact parsed input under canonical input bound. Native R2 constant and decoder multiplication/CtOption static source independently matched; private Scalar/Choice/CtOption/compiler/primitives/full native execution and Transfer remain owned OPEN.'
r=dict(status='PASSED',kind='Independent authenticated handwritten source/audit augmentation, exact R2 constant/use static association and semantic contract review',source=pin(S),fresh_reports=7,native_static_association=dict(library=pin(library),R2_words=words),scope=scope,full_transfer='OPEN',native_execution='UNRUN');(D/'semantic-source-review01.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status='PASSED',reports=7,R2_native_constant_exact=True)))
