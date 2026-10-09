"""Independently replay recovered input absorption and block chaining from candidate metadata."""
import pathlib,json,sqlite3,hashlib,copy,time,resource
if not __debug__:raise RuntimeError('optimized mode forbidden')
R=pathlib.Path(__file__).resolve().parents[2];O=pathlib.Path(__file__).parent;start=time.monotonic();resource.setrlimit(resource.RLIMIT_CPU,(60,60))
p=52435875175126190479447740508185965837690552500527637822603658699938581184513
def sha(f):
 h=hashlib.sha256()
 with f.open('rb') as s:
  while b:=s.read(1024**2):h.update(b)
 return h.hexdigest()
f=O/'qualified01.json';fh=sha(f);data=json.loads(f.read_text());D=R/'work/parent-full-program/capture/lowering-resume01.sqlite';assert sha(D)==data['database_sha256']
db=sqlite3.connect(D.resolve().as_uri()+'?mode=ro',uri=True);db.execute('PRAGMA cache_size=-16384');blocks={tuple(b['round1_span']):b for b in data['blocks']}
def node(i):return db.execute('SELECT op,lk,li,rk,ri FROM nodes WHERE id=?',(i,)).fetchone()
def scalar(i):return int(db.execute('SELECT value FROM constants WHERE id=?',(i,)).fetchone()[0],16)
def native(ref):return ['native',scalar(ref[1])] if ref[0]==0 else ref

def check(call):
 w=call['width'];arity=call['arity'];domain=call['domain'];assert w in [3,6] and (w==3)==(arity<=2);assert len(call['inputs'])==arity and 0<arity<=64 and 0<=domain<256
 assert call['IV']==256*arity+domain;assert len(call['permutations'])==(arity+w-2)//(w-1)
 state=[['native',call['IV']]]+[['native',0]]*(w-1);consumed=0
 for chunk in call['permutations']:
  b=blocks[tuple(chunk['round1_64_span'])];assert b['width']==w and b['round0_span']==chunk['round0_span']
  inputs=call['inputs'][consumed:consumed+w-1];assert inputs==chunk['chunk_inputs'];consumed+=len(inputs);ids=chunk['absorption_nodes'];ni=0
  for j,inp in enumerate(inputs,1):
   a=native(state[j]);c=native(inp)
   if a[0]==c[0]=='native':state[j]=['native',(a[1]+c[1])%p];continue
   if c[0]=='native':a,c=c,a
   assert ni<len(ids);i=ids[ni];ni+=1;actual=node(i)
   if a[0]=='native':assert actual[1]==0 and scalar(actual[2])==a[1];a=[0,actual[2]]
   assert actual==('add',*a,*c);state[j]=[2,i]
  assert ni==len(ids);assert ids==list(range(chunk['round0_span'][0]-len(ids),chunk['round0_span'][0]));assert state==b['before_round0'];state=b['final_state']
 assert consumed==arity and state==call['final_state'] and call['result']==state[1]
 return True
for call in data['calls']:assert check(call)
controls=[]
first=next(c for c in data['calls'] if c['domain']==23 and c['arity']==4);multi=next(c for c in data['calls'] if c['domain']==24 and c['arity']==6)
variants=[]
x=copy.deepcopy(first);x['inputs'][0],x['inputs'][1]=x['inputs'][1],x['inputs'][0];variants.append(('input_swap',x))
x=copy.deepcopy(first);x['domain']+=1;x['IV']+=1;variants.append(('domain',x))
x=copy.deepcopy(first);x['result']=x['final_state'][0];variants.append(('existing_wrong_output',x))
x=copy.deepcopy(multi);x['permutations'].pop();variants.append(('missing_continuation',x))
x=copy.deepcopy(multi);x['permutations'][1]=copy.deepcopy(x['permutations'][0]);variants.append(('duplicate_continuation',x))
x=copy.deepcopy(multi);x['inputs'][-1]=x['inputs'][0];x['permutations'][-1]['chunk_inputs'][-1]=x['inputs'][0];variants.append(('continuation_input',x))
for name,x in variants:
 try:check(x)
 except (AssertionError,KeyError,IndexError) as e:controls.append({'mutation':name,'same_checker_rejected':True})
 else:raise RuntimeError('accepted mutation '+name)
assert sha(f)==fh and sha(D)==data['database_sha256'];assert time.monotonic()-start<120 and resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<512*1024**2
r={'kind':'independent-candidate-absorption-chain-replay-data-only','candidate_sha256':fh,'database_sha256':data['database_sha256'],'accepted_hash_chains':188,'controls':controls,'seconds':time.monotonic()-start,'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'kernel_run':False,'proof_credit':0,'full_transfer':'OPEN'};(O/'chains-review01.json').write_text(json.dumps(r,indent=2)+'\n');print('PASS188 chains6controls',r['seconds'])
