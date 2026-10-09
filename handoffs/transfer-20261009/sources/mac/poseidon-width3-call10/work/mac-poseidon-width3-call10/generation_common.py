import hashlib,json,os,re
if not __debug__: raise RuntimeError("Optimized Python is unsupported")
from pathlib import Path
S=Path(__file__).resolve().parent;ROOT=S.parents[1];O=ROOT/'outputs/mac-poseidon-width3-call10';P=S/'project/ShielddSecurity'
sha=lambda b:hashlib.sha256(b).hexdigest()
def audited(text,module):
 names=re.findall(r'^theorem (\w+)',text,re.M)
 for name in reversed(names):
  start=re.search(r'^theorem '+name+r'\b',text,re.M).start();nxt=re.search(r'^(theorem|variable|def|end)\b',text[start+1:],re.M);assert nxt
  at=start+1+nxt.start();text=text[:at]+f'set_option pp.all true in\n#check @ShielddSecurity.{module}.{name}\n#print axioms ShielddSecurity.{module}.{name}\n\n'+text[at:]
 return text,names
def save(module,text):
 b=text.encode();p=P/(module+'.lean')
 if p.exists() and p.read_bytes()!=b:
  old=p.read_bytes();hist=O/'source-history';hist.mkdir(exist_ok=True);(hist/(module+'-'+sha(old)+'.lean')).write_bytes(old)
 tmp=p.with_suffix('.tmp');tmp.write_bytes(b);os.replace(tmp,p);return dict(module=module,source_sha256=sha(b),bytes=len(b))
def metadata(label,generator,files,extra=None):
 i=1
 while(O/f'{label}-generation{i:02d}.json').exists():i+=1
 payload=dict(generator_sha256=sha(Path(generator).read_bytes()),common_sha256=sha(Path(__file__).read_bytes()),sources=files,**(extra or {}));(O/f'{label}-generation{i:02d}.json').write_text(json.dumps(payload,indent=2)+'\n');print(json.dumps(payload))
DESCRIPTOR_SHA='01b68f32bf6896a6122805713cdd5448105d2aab2da056699c9d35dd57f162ff'
def descriptor():
 raw=(O/'rounds02.json').read_bytes();assert sha(raw)==DESCRIPTOR_SHA;return json.loads(raw)
def lc(ts):return '['+', '.join(f'({c},{v})' for c,v in ts)+']'
def row(r):return '⟨'+lc(r['a'])+','+lc(r['b'])+'⟩'
