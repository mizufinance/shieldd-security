from pathlib import Path
import json,hashlib,sys,re,os
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-canonical-comparisons216-source07'
def require(c,m):
 if not c:raise RuntimeError(m)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated preparation');require(not S.exists(),'fresh immutable maintained successor');v={'inputs':{},'modules':{},'scope':'Proof-only repair of exact recipeAt terminal equality: rfl uses direct kernel defeq, avoids absent Decidable Recipe. No statement or DATA change; preserves failed1260 source04 unqualified.'}
for i in [4,5]:
 P=W/('mac-canonical-comparisons216-source'+str(i).zfill(2));tp=P/'templates01.json';m=json.loads((P/'producer-manifest01.json').read_bytes());require(pin(tp)==m['templates01.json'],'exact frozen old template');q=json.loads(tp.read_bytes());v['inputs'].update(q['inputs']);v['inputs'][str(tp)]=pin(tp);v['inputs'][str(P/'producer-manifest01.json')]=pin(P/'producer-manifest01.json')
 for n,d in q['modules'].items():
  body,count=re.subn(r'(theorem terminal_checked[^\n]* := )by decide',r'\1by rfl',d['body']);require(count==1,'one exact terminal proof per root');v['modules'][n]={'body':body,'names':d['names']}
require(len(v['modules'])==14,'all14 exact comparisons');st=os.statvfs(W);require(st.f_bavail*st.f_frsize>2*1024**3+1024**2,'source disk reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'templates01.json').write_text(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
