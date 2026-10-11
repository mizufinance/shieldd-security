from pathlib import Path
import json,re,hashlib,ast
J=Path(__file__).parent;W=J.parent;D=J/'windows-finalization-object-frames-review01';P=D/'packet01';R=W/'runtime-snapshot';A=P/'context/known-finalization-source-association.json';v=json.loads(A.read_text())
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
sources={};checked=[]
for z in v['runtime_sources']:
 p=R/z['path'].split('shieldd-pr160-844389ee\\',1)[1].replace('\\','/');b=p.read_bytes();assert len(b)==z['bytes']and hashlib.sha256(b).hexdigest()==z['sha256'];sources[z['path']]=b.decode();checked.append(pin(p))
rows=v['keys'];assert len(rows)==6
expected=[('sct','block_materialization','delete'),('sct','cached_state_commitment_tree','put'),('compact','pending_routing_actions','delete'),('compliance','pending_user_registrations','delete'),('compliance','pending_user_status_changes','delete'),('compliance','pending_asset_registrations','delete')]
for row,(provider,name,operation)in zip(rows,expected):
 assert(row['provider'],row['function'],row['operation'])==(provider,name,operation)
 text=sources[row['key_source']['path']];expression=r'pub fn '+name+r'\(\) -> &\x27static str\s*\{\s*"([^"\n]+)"\s*\}';found=list(re.finditer(expression,text));assert len(found)==1
 match=found[0];assert match.group(1)==row['literal']and list(row['literal'].encode())==row['utf8']and text[:match.start()].count('\n')+1==row['line']
tree=next(t for p,t in sources.items()if p.endswith('sct\\src\\component\\tree.rs'));compact=next(t for p,t in sources.items()if p.endswith('compact-block\\src\\component\\manager.rs'));registry=next(t for p,t in sources.items()if p.endswith('compliance\\src\\registry.rs'))
assert tree.count('self.object_delete(state_key::cache::block_materialization());')==1 and tree.count('self.object_put(state_key::cache::cached_state_commitment_tree(), tree);')==1
assert compact.count('self.object_delete(state_key::pending_routing_actions());')==1
for name in ['pending_user_registrations','pending_user_status_changes','pending_asset_registrations']:assert f'let key = state_key::{name}();'in registry
# Execute only the original literal-source assembly, with rows independently authenticated above.
recipe=P/'qualified/prepare_recipe.py';nodes=ast.parse(recipe.read_text()).body;body=[]
for n in nodes:
 if isinstance(n,ast.Assign)and any(isinstance(t,ast.Name)and t.id in {'source','names'}for t in n.targets):body.append(n)
 elif isinstance(n,ast.For)and isinstance(n.iter,ast.Name)and n.iter.id=='names':body.append(n)
 elif isinstance(n,ast.AugAssign)and isinstance(n.target,ast.Name)and n.target.id=='source':body.append(n)
assert len(body)==4
template=body[0];assert ast.dump(template.value)==ast.dump(ast.parse(repr(template.value.func.value.value)+".replace('KEY_BYTES_LITERAL',repr([r['utf8'] for r in rows]))",mode='eval').body)
assert ast.dump(body[1].value)==ast.dump(ast.parse("re.findall(r'^(?:structure|def|theorem) ([A-Za-z0-9_]+)',source,re.M)",mode='eval').body)
assert len(body[2].body)==1 and isinstance(body[2].body[0],ast.AugAssign)and body[2].body[0].target.id=='source'
for n in body:
 for c in [x for x in ast.walk(n)if isinstance(x,ast.Call)]:
  assert (isinstance(c.func,ast.Name)and c.func.id=='repr')or(isinstance(c.func,ast.Attribute)and c.func.attr in {'replace','findall'}and isinstance(c.func.value,(ast.Name,ast.Constant)))
env={'rows':rows,'re':re};exec(compile(ast.Module(body=body,type_ignores=[]),str(recipe),'exec'),env);source=P/'source/ShielddSecurity/TransferFinalizationObjectFrames01.lean';assert env['source']==source.read_text()and len(env['names'])==8;assert not(P/'rejected').exists()
report=dict(status='PASSED',kind='Independent exact runtime key/mutator source association and pure maintained symbolic model assembly; first strict run passed',source=pin(source),recipe=pin(recipe),runtime_sources=checked,association=pin(A),fresh_reports=8,scope='All six named exact UTF8 object keys differ from pending key. Typed arbitrary finite mutations restrict keys via membership; existing putObject including deletion tombstones derives pending observation preservation by induction. Initial sealed object is supplied as precondition, then retained. Key projection injectivity and full native trace completeness/order/value/execution, other component effects, Any/Clone/Arc/cache/ownership/compiler/OS correspondence remain owned OPEN. No desired final field or per-step frame supplied.',full_transfer='OPEN',native_execution='UNRUN')
(D/'semantic-source-review01.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(dict(status='PASSED',reports=8,runtime_sources=len(checked),pure_source='EXACT')))
