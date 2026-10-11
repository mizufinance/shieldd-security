from pathlib import Path
import sys,json,re,hashlib
S=Path(__file__).resolve().parent
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated flags')
require(not(S/'producer-manifest01.json').exists()and not(S/'source-root').exists(),'immutable emission')
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);out=[]
for filename,mod,count in [('template.lean','ComparisonCertificate101',10)]:
 t=(S/filename).read_text();matches=list(re.finditer(r'^(?:noncomputable )?(?:def|theorem|abbrev|structure) (\w+)',t,re.M));require(len(matches)==count,'exact split declaration census');text=t[:matches[0].start()]
 for i,m in enumerate(matches):
  text+=t[m.start():matches[i+1].start()if i+1<len(matches)else len(t)]+'\n'+f'set_option pp.all true in\n#check @ShielddSecurity.ComparisonCertificate101.{m[1]}\n#print axioms ShielddSecurity.ComparisonCertificate101.{m[1]}\n'
 p=r/(mod+'.lean')
 with p.open('x')as f:f.write(text)
 out.append(dict(name=mod,source=pin(p),audits=['ShielddSecurity.ComparisonCertificate101.'+m[1]for m in matches],template=pin(S/filename)))
put('generation01.json',dict(generator=pin(Path(__file__)),outputs=out,scope='Fresh kernel qualification pending: split finite recipe check from full-relation import floor, identical mathematical range statements; no desired truth/native/fullTransfer.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(out))
