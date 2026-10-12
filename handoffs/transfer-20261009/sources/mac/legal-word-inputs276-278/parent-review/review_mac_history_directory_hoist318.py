from pathlib import Path
import ast,hashlib,json
J=Path(__file__).parent; W=J.parent
old=W/'mac-full-arithmetic45-execution304/maintained/guard.py';new=W/'mac-full-arithmetic45-execution307/maintained/guard.py'
pin=lambda p:dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
assert pin(old)['sha256']=='3d87e08778118242db98ab9d0d59f0318d8f978a812e6c247b49c471d9f121b4'
assert pin(new)['sha256']=='40dadbd3499694382bb3b9477c0ad99ecfa980b91c036d41da34ab42776e7022'
prior=J/'mac-alias-census-hoist-review307.json';assert json.loads(prior.read_text())['status']=='PASSED'
a=ast.parse(old.read_text());b=ast.parse(new.read_text())
f=next(n for n in ast.walk(a) if isinstance(n,ast.FunctionDef) and n.name=='verify_tree')
f.body.insert(1,ast.parse('link_maps={}').body[0])
loop=next(n for n in f.body if isinstance(n,ast.For) and ast.unparse(n.target)=='(parent, relative, link, identity)')
loop.body.insert(0,ast.parse('cancelled()').body[0]);branch=loop.body[1];assert isinstance(branch,ast.If)
assert ast.unparse(branch.body[-1])=="require(directory_link(p) == link, 'protected historical symlink')"
branch.body[-1:]=ast.parse("parent_dir=str(p.parent)\nif parent_dir not in link_maps:link_maps[parent_dir]=directory_snapshot(parent_dir)[1]\nrequire(link_maps[parent_dir].get(p.name)==link,'protected historical symlink')").body
assert ast.dump(a,include_attributes=False)==ast.dump(b,include_attributes=False)
# Execute the actual nested function in isolation, not the production guard main.
scratch=J/'history-directory-hoist-data318-source02';assert not scratch.exists();scratch.mkdir();root=scratch/'cache';root.mkdir();(root/'Own.olean').write_bytes(b'own')
g={'__name__':'SOURCE_DATA_ONLY','__file__':str(new)};exec(compile(new.read_bytes(),str(new),'exec'),g)
records={f'T{i:04d}.olean':{'target':{'path':str(root/'Own.olean')},'size':len(str(root/'Own.olean'))} for i in range(2048)}
g['preserved_alias_root']=lambda p:records if str(p)==str(root) else {}
g['preserved_configs']=lambda:{}
addition='/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-full-arithmetic45-execution186/config01.json'
g['config']={'history_closed_keyset_additions':{addition:{}}}
g['preserved_configs']=lambda:{addition:{'original':{}}}
node=next(n for n in ast.walk(b)if isinstance(n,ast.FunctionDef)and n.name=='verify_tree');exec(compile(ast.Module(body=[node],type_ignores=[]),str(new),'exec'),g)
checked=[];g['checked_pin']=lambda p:checked.append(p)
items=tuple((0,name,entry['target']['path'],entry['target']) for name,entry in records.items())+((0,'Own.olean',None,{'path':str(root/'Own.olean')}),)
shape=((str(root),),items,(),())
actual=g['directory_snapshot'];calls=[]
def snapshot(p):calls.append(str(p));return actual(p)
g['directory_snapshot']=snapshot
g['verify_tree'](shape)
# One phase_files snapshot, one local map load; every target remains checked.
assert len(calls)==2 and len(checked)==2049
g['checked_phase_close']()
# Incorrect target still fails; this is test data only.
bad=list(items);bad[0]=(0,bad[0][1],'wrong-target',bad[0][3])
try:g['verify_tree']((shape[0],tuple(bad),(),()));raise AssertionError('wrong link accepted')
except RuntimeError as e:assert str(e)=='protected historical symlink'
# Actual directory tokens detect a post-snapshot mutation at terminal close.
(root/'Changed').write_bytes(b'x')
try:g['checked_phase_close']();raise AssertionError('changed directory accepted')
except RuntimeError as e:assert str(e)=='directory changed after census'
# Cancellation remains before per-entry checking.
g['phase_files']=lambda p:(str(root)+'/'+i[1] for i in items);g['CANCELLED']=True
try:g['verify_tree'](shape);raise AssertionError('cancellation accepted')
except RuntimeError as e:assert str(e)=='cancellation requested'
report=dict(status='PASSED',baseline_guard=pin(old),successor_guard=pin(new),prior_review=pin(prior),controls=['2048 links: two total snapshots, every 2049 identity checked','wrong historical link refused','post-snapshot directory mutation refused at terminal close','per-entry cancellation refused'],scope='Only guard AST delta: finite per-tree parent-directory snapshot map and per-entry cancellation. Exact historical keysets, link targets, each target byte pin and terminal directory/inode rechecks retained. Local mapping is released after each finite historical tree. All other guard AST, physical admission/process/heap/disk limits unchanged. Isolated actual nested function and directory census exercised on Root-owned synthetic metadata only; no dispatcher/main/Lean or production mutation.',full_transfer='OPEN')
out=J/'mac-history-directory-hoist-review318.json';assert not out.exists();out.write_text(json.dumps(report,indent=2)+'\n');print('PASSED exact AST and four isolated controls')
