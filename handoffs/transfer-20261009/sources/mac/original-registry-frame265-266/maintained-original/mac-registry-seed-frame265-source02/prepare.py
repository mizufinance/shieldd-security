from pathlib import Path
import json,hashlib,sys,os,re,runpy
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');O=W/'mac-registry-seed-frame265-source01';S=W/'mac-registry-seed-frame265-source02';P=W/'mac-full-arithmetic45-execution293'
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):
 p=Path(p);b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def put(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'isolated source');require(not S.exists(),'immutable');old=json.loads((O/'templates01.json').read_bytes());body=old['modules']['SharedSeedShape265']['body'];pre='set_option autoImplicit false\nset_option maxHeartbeats 900000\nset_option maxRecDepth 8192\nnoncomputable section\n';namespace='namespace ShielddSecurity.SharedSeedShape265\n';end='end ShielddSecurity.SharedSeedShape265\n';shape=re.search(r'^abbrev Shape.*$',body,re.M).group(0)+'\n';lines=re.findall(r'^theorem (b\d+) : \((CapturedBooleanSlots208B\d+)\.slots.map Prod.snd\).*$',body,re.M);require(len(lines)==58,'exact58 original finite checks');mods={};mods['SharedSeedBase265']=dict(body='import ShielddSecurity.Compiler\n'+pre+namespace+shape+end,names=['SharedSeedShape265.Shape'],qualified_audits=True)
checks=[]
for i in range(0,58,8):
 part=lines[i:i+8];name='SharedSeedBatch265B'+str(i//8).zfill(2);imports=list(dict.fromkeys(n for _,n in part));proofs=[]
 for label,n in part:
  proof=re.search(r'^theorem '+label+r'.*$',body,re.M).group(0)+'\n';proofs.append(proof)
 mods[name]=dict(body='import ShielddSecurity.SharedSeedBase265\n'+''.join('import ShielddSecurity.'+n+'\n'for n in imports)+pre+namespace+''.join(proofs)+end,names=['SharedSeedShape265.'+label for label,_ in part],qualified_audits=True);checks.append(name)
word=re.search(r'^theorem word_checked.*$',body,re.M).group(0)+'\n';word=word.replace('SharedWordWitness221.wordSlots','(CapturedWordRoot213.words.map Prod.fst)')
mods['SharedSeedWord265']=dict(body='import ShielddSecurity.CapturedWordRoot213\n'+pre+namespace+word+end,names=['SharedSeedShape265.word_checked'],qualified_audits=True)
a=body.index('theorem boolean_shape');b=body.index('theorem word_checked');c=body.index('theorem seed_shape');root=body[a:b]+body[c:body.index(end)]
mods['SharedSeedShape265']=dict(body='import ShielddSecurity.SharedWordWitness221\n'+''.join('import ShielddSecurity.'+n+'\n'for n in ['SharedSeedBase265',*checks,'SharedSeedWord265'])+pre+namespace+root+end,names=['boolean_shape','seed_shape'])
mods['RegistrySeedFrame265']=old['modules']['RegistrySeedFrame265']
inputs=dict(old['inputs']);g=runpy.run_path(str(P/'maintained/guard.py'),run_name='SOURCE_ONLY');cfg=g['read_config'](str(P/'config01.json'),pin(P/'config01.json')['sha256']);q=json.loads(Path(cfg['closure']['path']).read_bytes())['modules'];q.update(cfg['qualified_batch_imports']);inputs[q['Compiler']['source']['path']]=q['Compiler']['source'];inputs[q['CapturedWordRoot213']['source']['path']]=q['CapturedWordRoot213']['source']
for f in ['templates01.json','generation01.json','producer-manifest01.json']:inputs[str(O/f)]=pin(O/f)
rp=P/'runtime/receipts/2362-SharedSeedShape265.json';r=json.loads(rp.read_bytes());require(r['status']=='failed'and r['exit']==-6 and r['cleanup']['clean'],'exact heap refusal preserved');inputs[str(rp)]=pin(rp);inputs[r['stderr']['path']]=r['stderr'];scope=dict(old['scope']);scope['repair']='2362 interpreter heap refusal: finite58 leaf checks split into8 narrow-import batches, separate scalar word-window check; generic Shape and opaque composition retained; frame body unchanged. Heap2048/RSS/time/thread safety unchanged.';scope['reports']=sum(len(d['names'])for d in mods.values())
require(scope['reports']==68,'all original planned68 declarations preserved once');require(os.statvfs(W).f_bavail*os.statvfs(W).f_frsize>=2*1024**3+4*1024**2,'source reserve');S.mkdir();(S/'prepare.py').write_bytes(Path(__file__).read_bytes());(S/'generate.py').write_bytes((W/'mac-candidate-batches262-source01/generate.py').read_bytes());put('templates01.json',dict(modules=mods,inputs=inputs,scope=scope));put('topology01.json',dict(order=['SharedSeedBase265',*checks,'SharedSeedWord265','SharedSeedShape265','RegistrySeedFrame265'],namespace='Original SharedSeedShape265 names exported from exact physical modules; no false object aliases',all_audits_unrun=True))
