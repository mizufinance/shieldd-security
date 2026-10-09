"""Two finite verified column transports of the immutable width6 tail template."""
import hashlib,json,os,re,sys
from pathlib import Path
if not __debug__:raise RuntimeError('Optimized Python unsupported')
S=Path(__file__).resolve().parent;R=S.parents[1]
O=Path(os.environ.get('TRANSFER_UPSTREAM_OUT',str(R/'outputs/mac-poseidon-width6-upstream11'))).resolve()
P=Path(os.environ.get('TRANSFER_UPSTREAM_PROJECT',str(S/'project/ShielddSecurity'))).resolve()
O.mkdir(parents=True,exist_ok=True);P.mkdir(parents=True,exist_ok=True)
h=lambda b:hashlib.sha256(b).hexdigest()
INPUT=Path(os.environ.get('TRANSFER_UPSTREAM_INPUT',str(R/'outputs/mac-poseidon-width6-upstream11/upstream01.json'))).resolve()
raw=INPUT.read_bytes();identity=h(raw)
FULL_SHA='3be245c6c55f473352481dbbc43d876591f8bbcedb61bd9c9c633de785112d6e'
COMPACT_SHA='74189456aa7380c35040e1c67d3b9d3ad48ce75d332ac80ad44971f1c0812ab9'
assert identity in [FULL_SHA,COMPACT_SHA], 'Unqualified generator input'
d=json.loads(raw)
if identity==COMPACT_SHA:assert d['schema']=='upstream11-portable-generation-v1' and d['full_descriptor_sha256']==FULL_SHA
assert d['runtime_sha']=='844389ee069e1fb2e576708842d0b389b4d9a44a'
assert d['parameter_sha256']=='84a51d11b64641fc3604b4cbedbe7cc82e91204b21d3bd62fb59462bbb4a5bb8'
assert len(d['prefix_scopes'])==4 and sum(len(x['nodes']) for x in d['prefix_scopes'])==377
assert len(d['indexed_original_rows'])==837 and len(d['input_terms'])==9
rows={r['capture_index']:r for r in d['indexed_original_rows']};assert len(rows)==837;sources=[]

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
