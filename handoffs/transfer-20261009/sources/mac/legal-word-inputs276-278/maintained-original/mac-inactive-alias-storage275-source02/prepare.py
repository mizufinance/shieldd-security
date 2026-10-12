from pathlib import Path
import os,sys,json,hashlib,ast,difflib
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');A=W/'mac-inactive-alias-storage275-source01';S=W/'mac-inactive-alias-storage275-source02';G=W/'mac-full-arithmetic45-execution302/maintained/guard.py'
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site and not sys.flags.optimize,'isolated source')
require(not S.exists(),'immutable successor');require(pin(G)['sha256']=='77e05e4eb1caeb76f58bf3dbfd45ebd7107391ac26b8ef2b464842c6d4e96b21','old guard');require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+1048576,'source disk floor')
helper=(A/'archive_aliases.py').read_text()
helper=helper.replace("with p.open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\\n');f.flush();os.fsync(f.fileno())", "with p.open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\\n');f.flush();os.fsync(f.fileno())\n fd=os.open(p.parent,os.O_RDONLY);os.fsync(fd);os.close(fd)")
helper=helper.replace("raw=subprocess.check_output(['/bin/ps','-axo','command='],text=True,timeout=5);", "raw=subprocess.check_output(['/bin/ps','-axo','pid=,command='],text=True,timeout=5);")
helper=helper.replace("roots=[];seen={}","roots=[];seen={};g['carried_check'](cfg);g['checked_phase_close']()")
helper=helper.replace("roots.append((directory,overlay,data,encoded))", "roots.append((directory,overlay,data,encoded));print(json.dumps(dict(census_phase=ordinal,roots=len(roots),links=sum(len(x[2])for x in roots))),flush=True)")
helper=helper.replace("(S/'archives').mkdir();directories={};reclaimed_links=0", "(S/'archives').mkdir();fd=os.open(S,os.O_RDONLY);os.fsync(fd);os.close(fd);directories={};reclaimed_links=0")
helper=helper.replace("directories[str(directory)]=record;put(S/('completed-root-'+str(i).zfill(4)+'.json'),record)","directories[str(directory)]=record;put(S/('completed-root-'+str(i).zfill(4)+'.json'),record);print(json.dumps(dict(preserved_root=i,roots=len(roots),links=reclaimed_links,free_disk=os.statvfs(W).f_bavail*os.statvfs(W).f_frsize)),flush=True)")
fragment=(A/'guard-fragment.py').read_text()
fragment=fragment.replace("root=str(root)\n checked_pin", "root=str(root)\n if not re.fullmatch(_ALIAS_DIRECTORY_PATTERN,root):return {}\n checked_pin")
fragment=fragment.replace("require(len(data['directories'])<=512", "require(isinstance(data['directories'],dict) and len(data['directories'])<=512")
fragment=fragment.replace("type(entry['mtime_ns'])is int", "type(entry['mode'])is int and type(entry['mtime_ns'])is int and entry['mtime_ns']>=0 and type(entry['size'])is int")
old=G.read_text();new=old.replace('def directory_snapshot(root):',fragment+'\ndef directory_snapshot(root):')
needle="    value=(tuple(entries),links)\n";replacement="    archived=preserved_alias_root(root)\n    require(not ({name for name,_,_ in entries}&set(archived)), 'archived input alias reappeared')\n    entries.extend((name,'link',v['size']) for name,v in archived.items())\n    links.update((name,v['target']['path']) for name,v in archived.items())\n"+needle
require(new.count(needle)==1,'exact directory insertion');new=new.replace(needle,replacement)
needle="                elif role=='link':\n                    require(key in aliases";replacement="                elif role=='link':\n                    if name in preserved_alias_root(parent):continue # honestly absent historical aliases: no physical byte charge\n                    require(key in aliases"
require(new.count(needle)==1,'exact physical census insertion');new=new.replace(needle,replacement)
# Companion absences for newly added qualified records are explicit too, including optional own .ir.
needle="        for identity in m['current_slots'].values():\n            if identity is not None: checked_pin(identity)\n";replacement="        for suffix,identity in m['current_slots'].items():\n            require(suffix in SUFFIXES, 'qualified companion suffix')\n            path=pathlib.Path(m['object']['path']).parent/(name+suffix)\n            if identity is not None:\n                require(identity['path']==str(path),'qualified companion path');checked_pin(identity)\n            else:require(not path.exists() and not path.is_symlink(),'qualified companion absence')\n"
require(new.count(needle)==1,'exact qualified companion loop');new=new.replace(needle,replacement)
for body in [helper,new]:ast.parse(body)
S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'archive_aliases.py').write_text(helper);(S/'guard-candidate.py').write_text(new)
(S/'guard.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile=str(G),tofile='fresh-guard-after-immutable-alias-manifest')))
put('scope01.json',dict(status='SOURCE_ONLY_UNRUN',prior_guard=pin(G),preserve_phases=list(range(1,302)),mechanism='Lossless exact inherited-input symlink metadata archive; virtual historical keysets ONLY. Objects/source/receipts/logs remain exact. Actual disk census excludes honestly absent aliases, counts archive/code/index. Current/future own cache is never virtual.',pending='Run isolated finite source-helper DATA controls, freeze, idle-only archive preservation, fill exact resulting manifest pin in separate immutable execution guard.',safety='No physical/per-run/one-heavy-process safeguard changes. No Lean replay. All original attempts/failures preserved.',supported_restore='Recreate recorded symlink target and lstat mode/mtime; verify target SHA/bytes first. Historical receipt source/object path identities remain original; aliases were no qualification.'))
put('source-producer01.json',{str(p.relative_to(S)):pin(p)for p in S.iterdir()if p.is_file()});print(json.dumps(dict(stage=str(S),bytes=sum(p.stat().st_size for p in S.iterdir()),producer=pin(S/'source-producer01.json'))))
