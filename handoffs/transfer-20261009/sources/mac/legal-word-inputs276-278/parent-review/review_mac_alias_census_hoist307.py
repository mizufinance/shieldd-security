from pathlib import Path
import ast, copy, hashlib, json
J=Path(__file__).parent;W=J.parent
old=W/'mac-full-arithmetic45-execution303/maintained/guard.py'
new=W/'mac-full-arithmetic45-execution304/maintained/guard.py'
pin=lambda p:dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
assert pin(old)['sha256']=='888bb69348a545de15a4e1a2eba2b62ca422289e7cc19d7bbc156c9293957567'
assert pin(new)['sha256']=='3d87e08778118242db98ab9d0d59f0318d8f978a812e6c247b49c471d9f121b4'
for name in ['mac-inactive-alias-preservation-review299.json','mac-storage-fixture-identity-review302.json']:
    assert json.loads((J/name).read_text())['status']=='PASSED'
a=ast.parse(old.read_text());b=ast.parse(new.read_text())
fn=next(n for n in a.body if isinstance(n,ast.FunctionDef)and n.name=='bytes_in')
loop=next(n for n in ast.walk(fn)if isinstance(n,ast.While))
assert ast.unparse(loop.test)=='pending'
loop.body.insert(0,ast.parse('cancelled()').body[0])
position=next(i for i,n in enumerate(loop.body)if isinstance(n,ast.For))
loop.body.insert(position,ast.parse('archived_names=preserved_alias_root(parent)').body[0])
matches=[n for n in ast.walk(loop)if isinstance(n,ast.Compare)and ast.unparse(n)=='name in preserved_alias_root(parent)']
assert len(matches)==1;matches[0].comparators=[ast.Name(id='archived_names',ctx=ast.Load())]
assert ast.dump(a,include_attributes=False)==ast.dump(b,include_attributes=False)

# Isolated actual census functions; replace only the archived-link provider.
# Synthetic names here are test data, never qualification inputs.
scratch=J/'alias-census-hoist-data307';assert not scratch.exists();scratch.mkdir()
root=scratch/'cache';root.mkdir();(root/'Own.olean').write_bytes(b'own')
g={'__name__':'SOURCE_DATA_ONLY','__file__':str(new)}
exec(compile(new.read_bytes(),str(new),'exec'),g)
records={f'T{i:04d}.olean':{'target':{'path':str(root/'Own.olean')},'size':len(str(root/'Own.olean'))}for i in range(2048)}
calls=[]
def provider(p):
    calls.append(str(p));return records if str(p)==str(root)else {}
g['preserved_alias_root']=provider
assert g['bytes_in'](root,{})==(3,0) and len(calls)==2
g['checked_phase_close']()
g['CANCELLED']=True
try:
    g['bytes_in'](root,{})
    raise AssertionError('cancellation accepted')
except RuntimeError as e:
    assert str(e)=='cancellation requested'
report=dict(status='PASSED',baseline_guard=pin(old),successor_guard=pin(new),source_review=pin(J/'mac-inactive-alias-preservation-review299.json'),fixture_addendum=pin(J/'mac-storage-fixture-identity-review302.json'),independent_cases=[dict(case='cold-cache-disabled-2048-logical-links',archive_lookups=len(calls),physical_bytes=3),dict(case='cancellation-before-directory-census',refused=True)],scope='Exact only AST delta: cancellation poll before each directory, one archived-name lookup before each directory entry loop, and identical membership predicate against that retained per-directory mapping. All other guard AST, provenance checks and physical verifier limits unchanged. Actual census functions repeated on isolated Root-owned synthetic data with archived provider replaced solely to count uncached calls; two lookups for2048logical links, no per-link archive decode; cancellation refused. No guard main/dispatcher/Lean or production input mutation.',full_transfer='OPEN')
out=J/'mac-alias-census-hoist-review307.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n')
print('PASSED exact per-directory hoist/cancellation; two isolated controls')
