from pathlib import Path
import ast,hashlib,json,lzma,os,sys,time,stat
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');PRE=W/'mac-full-arithmetic45-execution220';S=W/'mac-accounting-cache221-source01'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site and not sys.flags.optimize,'isolated flags')
source=(PRE/'maintained/guard.py').read_text();tree=ast.parse(source)
needed={'require','sha','strict_json','preserved_configs','read_pin','checked_pin','history_pool','history_size','history_shape','bytes_in','overlay_map','data_fixture_aliases'}
assign={'_STORAGE_PIN','_STORAGE','_CHECKED','_ARCHIVE_PROOFS','_HISTORY_POOL','_HISTORY_POOL_BYTES','_HISTORY_SHARED_IDS','_HISTORY_TREES','_HISTORY_TREE_BYTES'}
body=[n for n in tree.body if isinstance(n,(ast.Import,ast.ImportFrom)) or isinstance(n,ast.FunctionDef) and n.name in needed or isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id in assign for t in n.targets)]
g={};exec(compile(ast.Module(body=body,type_ignores=[]),'selected-guard-primitives','exec'),g)
c=json.loads((PRE/'config01.json').read_bytes());t=time.monotonic();seen={};total_entries=0;old={};new={}
def walk(identity):
 global total_entries
 key=identity['path'];require(key not in seen,'history tree cycle/shared-node observation')
 h=g['strict_json'](g['read_pin'](identity));seen[key]=identity
 for parent in h.get('parents',[]):walk(parent)
 expected=h.get('historical_aliases',{})
 derived={path:item['target']for path,item in h['entries'].items() if 'symlink_target'in item}
 require(expected==derived,'literal alias map exactly reconstructed from protected links '+key)
 old.update(expected);new.update(derived);total_entries+=len(h['entries'])
walk(c['carried_failure']);require(old==new,'complete historical alias map')
legacy_seconds=time.monotonic()-t
helper='''def accounting_history_aliases(identity):
    # Metadata shape is byte-pinned before reuse; no source/object bytes cached.
    shape=history_shape(identity); roots,items,parents,_=shape
    result={}
    for parent in parents: result.update(accounting_history_aliases(parent))
    for parent,relative,link,target in items:
        if link is not None:
            require(link==target['path'], 'exact absolute historical accounting link')
            result[roots[parent]+'/'+relative]=target
    return result

'''
g2=dict(g);exec(helper,g2);t=time.monotonic();computed=g2['accounting_history_aliases'](c['carried_failure']);require(computed==old,'shape accounting parity cold');cold=time.monotonic()-t
t=time.monotonic();computed=g2['accounting_history_aliases'](c['carried_failure']);require(computed==old,'shape accounting parity warm');warm=time.monotonic()-t
# No followed directory links; one lstat per physical item, metadata suffixes unchanged.
bytehelper='''def bytes_in(root, aliases):
    root=os.fspath(root); total=metadata=0
    if os.path.exists(root):
        pending=[(root,())]
        while pending:
            directory,parts=pending.pop()
            with os.scandir(directory) as items:
                for item in items:
                    st=item.stat(follow_symlinks=False); relative=parts+(item.name,)
                    if stat.S_ISLNK(st.st_mode):
                        require(item.path in aliases and os.readlink(item.path)==aliases[item.path]['path'], 'unapproved batch symlink')
                        total+=st.st_size
                    elif stat.S_ISDIR(st.st_mode): pending.append((item.path,relative))
                    elif stat.S_ISREG(st.st_mode):
                        total+=st.st_size
                        if 'runtime' in relative or pathlib.PurePath(item.name).suffix in {'.json','.jsonl','.log','.stdout','.stderr'}: metadata+=st.st_size
    return total,metadata

'''
g2['stat']=stat;exec(bytehelper,g2)
aliases={**old,**g['overlay_map'](c),**g['data_fixture_aliases'](c)}
t=time.monotonic();before=[g['bytes_in'](root,aliases)for root in c['charged_roots']];beforetime=time.monotonic()-t
t=time.monotonic();after=[g2['bytes_in'](root,aliases)for root in c['charged_roots']];aftertime=time.monotonic()-t
# Runtime is live. Immutable root counts must match; mutable batch excluded from parity.
for root,x,y in zip(c['charged_roots'],before,after):
 if root!=str(PRE):require(x==y,'exact accounting parity '+root)
require(not S.exists(),'new source-only primitive stage');S.mkdir()
(S/'accounting-helper.py').write_text(helper+bytehelper)
(S/'data_controls.py').write_bytes(Path(__file__).read_bytes())
report=dict(scope='AST-selected pure metadata/filesystem primitives only; no guard entrypoint or verifier launched',legacy_history_seconds=legacy_seconds,cold_shape_seconds=cold,warm_shape_seconds=warm,histories=len(seen),entries=total_entries,aliases=len(old),pool_bytes=g2['_HISTORY_POOL_BYTES'],tree_bytes=g2['_HISTORY_TREE_BYTES'],old_census_seconds=beforetime,new_census_seconds=aftertime,roots=len(before),immutable_roots_exact=True,live_root_counts=dict(old=before[c['charged_roots'].index(str(PRE))],new=after[c['charged_roots'].index(str(PRE))]),helper=pin(S/'accounting-helper.py'),predecessor=pin(PRE/'maintained/guard.py'),zero_formal_credit=True)
(S/'data-report01.json').write_text(json.dumps(report,sort_keys=True,separators=(',',':'))+'\n');print(json.dumps(report))
