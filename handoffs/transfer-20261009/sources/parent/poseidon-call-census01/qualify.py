"""Exact forward source-pattern and absorption-chain data checks; not formal refinement."""
import pathlib,json,hashlib,sqlite3,time,resource,copy,subprocess
if not __debug__:raise RuntimeError('optimized mode forbidden')
R=pathlib.Path(__file__).resolve().parents[2];O=pathlib.Path(__file__).parent;start=time.monotonic();resource.setrlimit(resource.RLIMIT_CPU,(60,60))
p=52435875175126190479447740508185965837690552500527637822603658699938581184513
def sha(f):
 h=hashlib.sha256()
 with f.open('rb') as s:
  while b:=s.read(1024**2):h.update(b)
 return h.hexdigest()
D=R/'work/parent-full-program/capture/lowering-resume01.sqlite';dh=sha(D);assert dh=='da9026b92d643ea8cddaf560b06bc783b291f152f799b48cc836290f57ed9f7d'
probe=O/'probe01.json';ph=sha(probe);v=json.loads(probe.read_text());assert not v['failures'] and len(v['accepted'])==210
censusfile=R/'work/parent-poseidon-census01/result03.json';ch=sha(censusfile);census=json.loads(censusfile.read_text());assert census['database_sha256']==dh
assert len(census['matches'])==210 and not census['rejected_candidates']
db=sqlite3.connect(D.resolve().as_uri()+'?mode=ro',uri=True);db.execute('PRAGMA cache_size=-16384');params={};parameter_hashes={}
for w,file in [(3,'poseidon381.json'),(6,'poseidon381-wide.json')]:
 f=R/'work/runtime-snapshot/crates/crypto/primitives/params'/file;b=subprocess.check_output(['git','show','844389ee069e1fb2e576708842d0b389b4d9a44a:crates/crypto/primitives/params/'+file],cwd=R/'work/runtime-snapshot');assert b==f.read_bytes();parameter_hashes[file]=sha(f);d=json.loads(b);params[w]=([[int(x,16)for x in row] for row in d['ark']],[[int(x,16)for x in row] for row in d['mds']])
def node(i):return db.execute('SELECT op,lk,li,rk,ri FROM nodes WHERE id=?',(i,)).fetchone()
def constant(i):return int(db.execute('SELECT value FROM constants WHERE id=?',(i,)).fetchone()[0],16)
def forward(before,ark,mds,begin,end,records,constants,first_constant,after,expected_next_constant):
 current=begin;ci=first_constant;used=[]
 def merge(op,a,b):
  nonlocal current,ci
  if a[0]==b[0]=='native':return ('native',(a[1]+b[1] if op=='add' else a[1]*b[1])%p)
  if b[0]=='native':a,b=b,a
  if a[0]=='native':assert constants[ci]==a[1],('constant',ci);a=(0,ci);ci+=1
  assert records[current]==(op,*a,*b),('node',current);used.append(current);current+=1;return (2,current-1)
 state=[merge('add',tuple(a),('native',c))for a,c in zip(before,ark)]
 for i,a in enumerate(state):
  sq=merge('mul',a,a);state[i]=merge('mul',merge('mul',sq,sq),a)
 ns=[]
 for row in mds:
  total=('native',0)
  for coef,a in zip(row,state):total=merge('add',total,merge('mul',('native',coef),a))
  ns.append(total)
 assert ns==[tuple(x)for x in after] and current==end and ci==expected_next_constant
 return len(used)
blocks=[];controls=[]
for record in sorted(v['accepted'],key=lambda x:x['round1_span']):
 w=record['width'];begin=record['round0_visited_nodes'][0];end=record['round1_span'][0];first=node(begin)[2];nextc=node(end)[2]
 records={i:tuple(r)for i,*r in db.execute('SELECT id,op,lk,li,rk,ri FROM nodes WHERE id>=? AND id<? ORDER BY id',(begin,end))};constants=dict((i,int(x,16))for i,x in db.execute('SELECT id,value FROM constants WHERE id>=? AND id<?',(first,nextc)))
 ark,mds=params[w];n=forward(record['before_round0'],ark[0],mds,begin,end,records,constants,first,record['after_round0'],nextc)
 b=copy.deepcopy(record);b.update(round0_span=[begin,end-1],round0_node_count=n,round0_constant_interval=[first,nextc-1],exact_forward_match=True);blocks.append(b)
 if not any(x['width']==w for x in controls):
  variants=[]
  rs=records.copy();row=list(rs[begin]);row[0]='mul';rs[begin]=tuple(row);variants.append(('opcode',record['before_round0'],ark[0],mds,rs,constants))
  cs=constants.copy();cs[first]=(cs[first]+1)%p;variants.append(('native_constant',record['before_round0'],ark[0],mds,records,cs))
  aks=ark[0].copy();aks[0]=(aks[0]+1)%p;variants.append(('ARK0',record['before_round0'],aks,mds,records,constants))
  ms=copy.deepcopy(mds);ms[0][0]=(ms[0][0]+1)%p;variants.append(('MDS',record['before_round0'],ark[0],ms,records,constants))
  bs=copy.deepcopy(record['before_round0']);assert bs[0][0]=='native';bs[0][1]+=1;variants.append(('IV',bs,ark[0],mds,records,constants))
  rs=records.copy();del rs[end-1];variants.append(('missing_final_node',record['before_round0'],ark[0],mds,rs,constants))
  for name,bs,aks,ms,rs,cs in variants:
   try:forward(bs,aks,ms,begin,end,rs,cs,first,record['after_round0'],nextc)
   except (AssertionError,KeyError) as e:controls.append({'width':w,'mutation':name,'same_forward_matcher_rejected':True,'reason':str(e)[:100]})
   else:raise RuntimeError('mutation accepted '+name)
 assert time.monotonic()-start<120 and resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<512*1024**2
by_previous={};heads=[]
for b in blocks:
 before=b['before_round0'][0]
 if before[0]=='native':heads.append(b)
 else:
  key=tuple(before);assert key not in by_previous;by_previous[key]=b
used=set();calls=[]
for head in heads:
 w=head['width'];iv=head['before_round0'][0][1];arity,domain=divmod(iv,256);assert 0<arity<=64 and (w==3)==(arity<=2)
 current=head;previous=[['native',iv]]+[['native',0]]*(w-1);inputs=[];chain=[];remaining=arity
 while True:
  key=current['round1_span'][0];assert key not in used;used.add(key);chunk=min(remaining,w-1);absorptions=[]
  assert current['before_round0'][0]==previous[0]
  for i in range(1,w):
   port=current['before_round0'][i];prior=previous[i]
   if i>chunk:assert port==prior;continue
   if prior[0]==port[0]=='native':inp=['native',(port[1]-prior[1])%p]
   else:
    assert port[0]==2;op,lk,li,rk,ri=node(port[1]);assert op=='add';a=[lk,li];b=[rk,ri]
    if prior[0]=='native':assert lk==0 and constant(li)==prior[1];inp=b
    elif a==prior:inp=b
    else:assert b==prior;inp=a
    absorptions.append(port[1])
   inputs.append(inp)
  if absorptions:assert absorptions==list(range(current['round0_span'][0]-len(absorptions),current['round0_span'][0]))
  chain.append({'round0_span':current['round0_span'],'round1_64_span':current['round1_span'],'absorption_nodes':absorptions,'chunk_inputs':inputs[-chunk:]})
  remaining-=chunk
  if not remaining:break
  previous=current['final_state'];current=by_previous[tuple(previous[0])];assert current['width']==w
 assert len(inputs)==arity
 calls.append({'width':w,'domain':domain,'arity':arity,'IV':iv,'inputs':inputs,'permutations':chain,'final_state':current['final_state'],'result':current['final_state'][1]})
assert len(used)==210 and len(calls)==188
assert sha(D)==dh and sha(probe)==ph and sha(censusfile)==ch
out={'kind':'qualified-source-pattern-hash-chain-census-data-only','runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','database_sha256':dh,'inherited_round1_64_census_sha256':ch,'round0_candidate_probe_sha256':ph,'parameter_sha256':parameter_hashes,'calls':calls,'blocks':blocks,'controls':controls,'counts':{'hash_chains':len(calls),'permutations':len(blocks),'continuations':len(blocks)-len(calls),'new_round0_nodes':sum(b['round0_node_count']for b in blocks)},'seconds':time.monotonic()-start,'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'kernel_run':False,'proof_credit':0,'limits':['Covers all210 permutations in inherited pattern census, not an independent claim of all possible runtime calls.','Domain/arity/input IDs/absorption and continuation joins are exact captured source-pattern data.','No Rust source callsite identity, Lean semantic/input completeness, compiler or parent-R1CS inclusion credit.','Native folded constants are inferred candidate values then matched by exact forward generation.'],'full_transfer':'OPEN'}
(O/'qualified01.json').write_text(json.dumps(out,indent=2)+'\n');print(out['counts']);print('controls',len(controls),'seconds',out['seconds'],'rss',out['peak_rss_bytes'])
