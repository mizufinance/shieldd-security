from pathlib import Path
import json,hashlib,sys,os,re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-merkle-local229-source03';S=W/'mac-merkle-local229-source04'
def require(c,m):
 if not c:raise RuntimeError(m)
def pin(p):
 b=Path(p).read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated preparation');require(not S.exists(),'fresh source');v=json.loads((P/'templates01.json').read_bytes());require(json.loads((P/'producer-manifest01.json').read_bytes())['templates01.json']==pin(P/'templates01.json'),'exact predecessor');d=v['modules'].pop('CapturedMerkleLocal229Pilot');b=d['body'].replace('CapturedMerkleLocal229Pilot','CapturedMerkleLocal229Single').replace('take 16','take 1').replace("List.range' 3890 16","List.range' 3890 1").replace('rows.length=16','rows.length=1');a=b.index('def localParent :');z=b.index('\ndef localCheck',a);first=b[a:z].splitlines()[1];b=b[:a]+'def localParent : Nat → Option Row\n'+first+'\n | _ => none'+b[z:];a=b.index(' change position ∈ [3890');z=b.index('\ntheorem check_congr',a);b=b[:a]+''' change position ∈ [3890] at member
 have same:=List.mem_singleton.mp member
 subst position
 rfl
'''+b[z:];d['body']=b;v['modules']={'CapturedMerkleLocal229Single':d};v['inputs'][str(P/'templates01.json')]=pin(P/'templates01.json');v['scope']='SOURCE_ONLY_UNRUN one dense row3890; exact trimmed target, literal single original-row branch, rfl global positional equality plus kernel finite checker. Isolates per-row cost without increasing heap or replaying accepted modules. All failed16/32/64 sources retained.'
require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>2*1024**3+1048576,'disk reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
