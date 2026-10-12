from pathlib import Path
import ast,json,hashlib,os,pathlib,stat,sys,tempfile
J=Path(__file__).parent;W=J.parent;baseline=W/'mac-full-arithmetic45-execution238/maintained/guard.py';candidate=W/'mac-full-arithmetic45-execution243/maintained/guard.py';fixture=W/'mac-directory-census-cache219b-source01';manifest=json.loads((fixture/'producer-manifest01.json').read_text())
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
for name,e in manifest['files'].items():assert pin(fixture/name)==e
assert manifest['links']=={'fixtures/ordinary/dir-link':str(fixture/'fixtures/ordinary/sub'),'fixtures/ordinary/link':str(fixture/'fixtures/other-target')}
for name,target in manifest['links'].items():assert (fixture/name).is_symlink()and os.readlink(fixture/name)==target
changed={'carried_check','phase_files','checked_phase_close','fixed_check','bytes_in','bounds'};added={'directory_token','directory_snapshot','directory_link','directory_phase_close','directory_fixture_aliases'}
def norm(p):
 t=ast.parse(p.read_text());out=[]
 for n in t.body:
  if isinstance(n,ast.Import):n.names=[v for v in n.names if v.name!='stat']
  if isinstance(n,ast.FunctionDef)and n.name in changed|added:continue
  if isinstance(n,ast.Assign)and any(isinstance(v,ast.Name)and v.id.startswith('_DIRECTORY_')for v in n.targets):continue
  out.append(ast.dump(n,include_attributes=False))
 return out
assert norm(baseline)==norm(candidate)
t=ast.parse(candidate.read_text());func={n.name:n for n in t.body if isinstance(n,ast.FunctionDef)}
for name in ['carried_check','fixed_check','checked_phase_close','bounds']:
 s=ast.unparse(func[name]);assert 'directory_' in s.lower()
assert 'total <= 2 * 1024 * 1024 * 1024' in ast.unparse(func['bounds'])and 'memory >= 15' in ast.unparse(func['bounds'])
def require(ok,msg):
 if not ok:raise ValueError(msg)
names={'history_size','directory_token','directory_snapshot','directory_link','directory_phase_close','phase_files','bytes_in'};nodes=[n for n in t.body if isinstance(n,ast.FunctionDef)and n.name in names];ns=dict(os=os,pathlib=pathlib,stat=stat,sys=sys,require=require,_HISTORY_SHARED_IDS=set(),_DIRECTORY_CACHE={},_DIRECTORY_CACHE_BYTES=0,_DIRECTORY_PHASE={});exec(compile(ast.Module(body=nodes,type_ignores=[]),'<isolated-directory-census-functions>','exec'),ns)
old=next(n for n in ast.parse(baseline.read_text()).body if isinstance(n,ast.FunctionDef)and n.name=='bytes_in');oldns=dict(pathlib=pathlib,os=os,require=require);exec(compile(ast.Module(body=[old],type_ignores=[]),'<old-independent-byte-census>','exec'),oldns);controls=[]
with tempfile.TemporaryDirectory(prefix='root-directory-review-',dir=J)as temp:
 root=Path(temp)/'ordinary';root.mkdir();(root/'sub').mkdir();(root/'a.json').write_text('abc');(root/'sub/x').write_text('abcd');target=Path(temp)/'target';target.write_text('z');link=root/'link';link.symlink_to(target);directory=root/'dir-link';directory.symlink_to(root/'sub');aliases={str(link):{'path':str(target)},str(directory):{'path':str(root/'sub')}}
 assert ns['bytes_in'](root,aliases)==oldns['bytes_in'](root,aliases);assert set(ns['phase_files'](root))=={str(p)for p in root.rglob('*')if p.is_file()or p.is_symlink()};ns['directory_phase_close']();controls.append('initial-file-link-directory-census-equal')
 ns['_DIRECTORY_PHASE'].clear();before=ns['directory_snapshot'](root);assert ns['directory_snapshot'](root) is before;ns['directory_phase_close']();controls.append('unchanged-directory-token-cache-hit')
 ns['_DIRECTORY_PHASE'].clear();(root/'a.json').write_text('abcdefghijk');assert ns['bytes_in'](root,aliases)==oldns['bytes_in'](root,aliases);ns['directory_phase_close']();controls.append('regular-file-size-fresh-despite-directory-cache')
 ns['_DIRECTORY_PHASE'].clear();ns['directory_snapshot'](root);(root/'added').write_text('x')
 try:ns['directory_phase_close']()
 except ValueError:controls.append('within-phase-addition-refused')
 else:raise AssertionError('addition')
 ns['_DIRECTORY_PHASE'].clear();assert str(root/'added')in set(ns['phase_files'](root));ns['directory_phase_close']();controls.append('next-phase-addition-freshly-observed')
 ns['_DIRECTORY_PHASE'].clear();ns['directory_snapshot'](root);link.unlink();link.symlink_to(root/'a.json')
 try:ns['directory_link'](link)
 except ValueError:controls.append('within-phase-link-replacement-refused')
 else:raise AssertionError('link-replacement')
 ns['_DIRECTORY_PHASE'].clear()
 try:ns['bytes_in'](root,aliases)
 except ValueError:controls.append('changed-link-target-refused-against-exact-alias')
 else:raise AssertionError('alias')
 ns['_DIRECTORY_PHASE'].clear()
 try:ns['directory_token'](directory)
 except ValueError:controls.append('symlink-root-refused')
 else:raise AssertionError('symlink-root')
 ns['_DIRECTORY_PHASE'].clear();link.unlink();(root/'a.json').unlink();(root/'a.json').symlink_to(target)
 try:ns['bytes_in'](root,aliases)
 except ValueError:controls.append('cached-regular-file-replaced-by-symlink-refused')
 else:raise AssertionError('file-type')
r=dict(status='PASSED',baseline=pin(baseline),successor=pin(candidate),retained_fixture=pin(fixture/'producer-manifest01.json'),independent_controls=controls,scope='Bounded128MiB directory-entry/name/role/link-target cache only; regular file sizes/hashes remain fresh. Ordinary directory full inode/change token verified before use and at phase close; changed keyset/alias/file type refused. Exact two retained DATA fixture aliases narrowly authenticated; no source/object/import shortcut. Existing physical RAM15percent/disk2GiB/heap/thread/groupRSS/timeout/prelaunch/postflight gates unchanged. Pure temporary Root fixtures only; no Lean/worker state mutation',full_transfer='OPEN');(J/'mac-directory-census-guard-review24.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(dict(status='PASSED',controls=len(controls))))
