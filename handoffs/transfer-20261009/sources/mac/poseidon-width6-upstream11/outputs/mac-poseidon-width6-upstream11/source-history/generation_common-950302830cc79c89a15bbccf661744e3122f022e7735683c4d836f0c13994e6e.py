"""Two finite verified column transports of the immutable width6 tail template."""
import hashlib,json,os,re,sys
from pathlib import Path
if not __debug__:raise RuntimeError('Optimized Python unsupported')
S=Path(__file__).resolve().parent;R=S.parents[1];O=R/'outputs/mac-poseidon-width6-upstream11';P=S/'project/ShielddSecurity';h=lambda b:hashlib.sha256(b).hexdigest()
raw=(O/'upstream01.json').read_bytes();assert h(raw)=='3be245c6c55f473352481dbbc43d876591f8bbcedb61bd9c9c633de785112d6e';d=json.loads(raw);rows={r['capture_index']:r for r in d['indexed_original_rows']};sources=[]
def audited(text,module):
 names=re.findall(r'^theorem (\w+)',text,re.M)
 for n in reversed(names):
  start=re.search(r'^theorem '+n+r'\b',text,re.M).start();nxt=re.search(r'^(theorem|variable|def|end)\b',text[start+1:],re.M);assert nxt;at=start+1+nxt.start();text=text[:at]+f'set_option pp.all true in\n#check @ShielddSecurity.{module}.{n}\n#print axioms ShielddSecurity.{module}.{n}\n\n'+text[at:]
 return text
def save(module,text,audit=False):
 if audit:text=audited(text,module)
 b=text.encode();p=P/(module+'.lean')
 if p.exists() and p.read_bytes()!=b:
  hist=O/'source-history';hist.mkdir(exist_ok=True);old=p.read_bytes();(hist/(module+'-'+h(old)+'.lean')).write_bytes(old)
 tmp=p.with_suffix('.tmp');tmp.write_bytes(b);os.replace(tmp,p);sources.append(dict(module=module,sha256=h(b),bytes=len(b)))
def lc(ts):return '['+', '.join(f'({c},{v})' for c,v in ts)+']'
def row(v):return '⟨'+lc(v['a'])+','+lc(v['b'])+'⟩'
