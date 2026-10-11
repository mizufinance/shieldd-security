from pathlib import Path
import json,hashlib,re,io,contextlib
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');S=Path(__file__).resolve().parent
items=[('mac-arithmetic-coefficients39-source01','ArithmeticCoefficients39C'+str(i).zfill(2),190+i)for i in range(8)]+[('mac-arithmetic-coefficients39-source01','ArithmeticCoefficients39',198),('mac-arithmetic-transport41-source01','CompilerArithmeticTransport41',200)]
def require(x,m):
 if not x:raise ValueError(m)
def pin(p):b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def write(n,v):
 with(S/n).open('x')as f:f.write(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n')
def replay(q):
 gen=q/'generate.py';captured={};oldopen=Path.open;oldmkdir=Path.mkdir
 class Sink:
  def __init__(self,p,mode):self.p=p;self.buffer=io.BytesIO()if'b'in mode else io.StringIO()
  def __enter__(self):return self.buffer
  def __exit__(self,*args):
   value=self.buffer.getvalue();captured[str(self.p)]=value if isinstance(value,bytes)else value.encode();self.buffer.close()
 def opened(path,mode='r',*args,**kwargs):
  if mode in('x','xb'):
   require(path==q/'generation01.json'or path in list(q.glob('source-root/ShielddSecurity/*.lean')),'exact generator sink');return Sink(path,mode)
  require(not any(c in mode for c in 'wa+'),'no other mutation');return oldopen(path,mode,*args,**kwargs)
 def mkdir(path,*args,**kwargs):require(path.is_dir(),'existing immutable output directory only')
 before={str(p):pin(p)for p in [gen,q/'generation01.json']+[p for p in [q/'template.lean',q/'coefficients01.json']if p.exists()]+list(q.glob('source-root/ShielddSecurity/*.lean'))}
 try:
  Path.open=opened;Path.mkdir=mkdir
  with contextlib.redirect_stdout(io.StringIO()):exec(compile(gen.read_bytes(),str(gen),'exec'),{'__file__':str(gen),'__name__':'__main__'})
 finally:Path.open=oldopen;Path.mkdir=oldmkdir
 require(len(captured)==len(list(q.glob('source-root/ShielddSecurity/*.lean')))+1 and all(Path(p).read_bytes()==b for p,b in captured.items()),'all generated source/metadata bytes exact')
 require(all(pin(Path(p))==v for p,v in before.items()),'old inputs unchanged')
 return dict(generator=pin(gen),template=pin(q/'template.lean')if(q/'template.lean').exists()else None,outputs=[dict(path=p,bytes=len(b),sha256=hashlib.sha256(b).hexdigest())for p,b in captured.items()],scope='Exact original maintained generator executed with exclusive writes captured only in memory; no second physical generated copy or Lean')
modules=[];audits=[];refs=[];replays=[]
for stage,name,index in items:
 q=R/'work'/stage;rp=q/f'runtime/receipts/{index}-{name}.json';d=json.loads(rp.read_bytes());require(d['status']=='passed'and type(d['exit'])is int and d['exit']==0 and d['cleanup']['clean'],'passed')
 src=Path(d['source']['path']);declared=re.findall(r'^\s*(?:def|theorem|inductive|abbrev) ([\w.]+)',src.read_text(),re.M);planned=re.findall(r'^#check @([\w.]+)',src.read_text(),re.M)
 require(len(declared)==len(planned)==len(d['audits'])and set(planned)=={a['name']for a in d['audits']},'complete own public declarations')
 for a in d['audits']:
  require(hashlib.sha256(a['full_type'].encode()).hexdigest()==a['full_type_sha256'],'full type hash');require(set(a['axioms'])<={'propext','Quot.sound','Classical.choice'},'standard axioms')
 audits+=d['audits'];modules.append(dict(module=name,receipt=pin(rp),source=d['source'],objects=d['objects'],stdout=d['stdout'],stderr=d['stderr'],cleanup=d['cleanup'],lean_seconds=d['lean_seconds'],peak_group_rss=d['peak_group_rss']))
 refs += [pin(q/x)for x in ['generate.py','template.lean','generation01.json','config01.json','prepare_continuation.py','maintained/guard.py','maintained-inventory01.json','coefficients01.json']if(q/x).exists()]
 for x in ['selected-data01.json','extract.py']:
  if(q/x).exists():refs.append(pin(q/x))
 
 if not any(x['generator']['path']==str(q/'generate.py')for x in replays):replays.append(replay(q))
require(len(audits)==29,'29 complete reports')
failures=[]
write('qualified-modules01.json',modules);write('full-audits01.json',audits);write('maintained-references01.json',refs);write('in-memory-replay01.json',replays)
last=json.loads(Path(modules[-1]['receipt']['path']).read_bytes());write('execution-census01.json',dict(accepted_modules=10,complete_reports=29,all_historical_attempts=last['all_attempts'],all_historical_seconds=last['all_lean_seconds'],failures=failures,counts_are_historical_accounting_not_project_quota=True))
write('scope01.json',dict(runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',source_context='cec1b30defc23497c8e9b30528dca12b09d328ea',storage='Eight balanced coefficient leaves plus global index dispatch; 7483 unique coefficients from all177954 arithmetic a-LCs; 1988002 terms in frozen stream',data=pin(R/'work/mac-arithmetic-coefficients39-source01/coefficients01.json'),historical_extraction_source=pin(Path('/tmp/prepare_coeff39.py')),generic_transport='Light canonical-row satisfaction transfer and derived four nonzero for pinned CharP, without Merkle-specific dependencies',premises=['Field F and CharP F pinnedp for transfer/four nonzero','Coefficient store itself has no semantic theorem; first/last finite values checked in eachleaf'],open=['Actual full177954 indexedprovider/partition/constructor','Deferred semantic assertions and verifier links','Native/global full Transfer correspondence'],inherited_custom_closure=last['inherited_closure'],official_closure=last['official_manifest']))
write('producer-manifest01.json',{str(p.relative_to(S)):pin(p)for p in S.iterdir()if p.is_file()});write('envelope01.json',dict(producer=pin(S/'producer-manifest01.json'),ordered34=pin(R/'work/mac-merkle-ordered34-kernel-result01/producer-manifest01.json')));write('postseal-guard01.json',dict(producer=pin(S/'producer-manifest01.json'),envelope=pin(S/'envelope01.json')));print(json.dumps(pin(S/'producer-manifest01.json')))
