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
require(pin(Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-registry-value-range97-source03/data-template.lean'))=={'path': '/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-registry-value-range97-source03/data-template.lean', 'sha256': 'b2498fc5fa8dd706a6aa4538dabc0bb2a462d68a44fc69248e5dbcf2a0568794', 'bytes': 2286},'exact inherited qualified maintained template');
require(pin(Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-registry-value-range97-source04/proof-template.lean'))=={'path': '/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-registry-value-range97-source04/proof-template.lean', 'sha256': 'd06c060d61ddb5ba0a6ab35d96999350d6c31221e80f1a18b1be948e718caf4c', 'bytes': 7253},'exact inherited qualified maintained template');
r=S/'source-root/ShielddSecurity';r.mkdir(parents=True);out=[]
for filename,mod,count in [('data-template.lean','CapturedRegistryNextRange114Data',8),('proof-template.lean','CapturedRegistryNextRange114',12)]:
 t=(S/filename).read_text();matches=list(re.finditer(r'^(?:noncomputable )?(?:def|theorem) (\w+)',t,re.M));require(len(matches)==count,'exact split declaration census');text=t[:matches[0].start()]
 for i,m in enumerate(matches):
  text+=t[m.start():matches[i+1].start()if i+1<len(matches)else len(t)]+'\n'+f'set_option pp.all true in\n#check @ShielddSecurity.CapturedRegistryNextRange114.{m[1]}\n#print axioms ShielddSecurity.CapturedRegistryNextRange114.{m[1]}\n'
 p=r/(mod+'.lean')
 with p.open('x')as f:f.write(text)
 out.append(dict(name=mod,source=pin(p),audits=['ShielddSecurity.CapturedRegistryNextRange114.'+m[1]for m in matches],template=pin(S/filename)))
put('generation01.json',dict(generator=pin(Path(__file__)),outputs=out,scope='NextValue255bit range and reconstructed original column13, actual positions178635..178890; standalone constructor only. Whole shared-frame and canonical assertion joins separate; no desired truth/native/fullTransfer.'))
put('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.rglob('*')if p.is_file()});put('envelope01.json',dict(producer=pin(S/'producer-manifest01.json')));put('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')))
print(json.dumps(out))
