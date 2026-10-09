"""Read-only exact source-pattern census of Poseidon rounds1..64; no proof credit."""
import argparse,hashlib,json,sqlite3,time,resource,subprocess
from pathlib import Path
if not __debug__:raise RuntimeError('optimized mode forbidden')
parser=argparse.ArgumentParser();parser.add_argument('--database',type=Path,required=True);parser.add_argument('--runtime',type=Path,required=True);parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
resource.setrlimit(resource.RLIMIT_CPU,(90,90))
# macOS does not support lowering RLIMIT_AS here; sample peak RSS per bounded block.
start=time.monotonic()
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(4*1024**2),b''):h.update(b)
 return h.hexdigest()
expected='da9026b92d643ea8cddaf560b06bc783b291f152f799b48cc836290f57ed9f7d'
assert digest(args.database)==expected
con=sqlite3.connect(args.database.resolve().as_uri()+'?mode=ro',uri=True);con.execute('PRAGMA query_only=ON');con.execute('PRAGMA cache_size=-16384')
p=52435875175126190479447740508185965837690552500527637822603658699938581184513
def match_records(width,begin,ark,mds,records,constants):
 count=7*(width+3*width+2*width*width)+57*(width+3+2*width*width)
 assert len(records)==count,'record_count'
 state=[(x[4],x[5])for x in records[:width]]
 assert all(kind==2 and node<begin for kind,node in state),'prior_ports'
 first_c=records[0][3]
 index=0;next_c=first_c;ports=[];consumed=[]
 def merge(op,a,b):
  nonlocal index,next_c
  if b[0]=='native':a,b=b,a
  if a[0]=='native':
   assert int(constants[next_c],16)==a[1],('constant',next_c)
   consumed.append((next_c,constants[next_c]));a=(0,next_c);next_c+=1
  actual=records[index];assert actual==(begin+index,op,*a,*b),('node',actual,op,a,b)
  index+=1;return (2,actual[0])
 for round_index in range(1,65):
  before=state.copy();round_start=begin+index
  state=[merge('add',v,('native',c))for v,c in zip(state,ark[round_index])]
  for j,v in enumerate(state):
   if round_index<4 or round_index>=61 or j==0:
    square=merge('mul',v,v);state[j]=merge('mul',merge('mul',square,square),v)
  ns=[]
  for row in mds:
   total=('native',0)
   for c,v in zip(row,state):total=merge('add',total,merge('mul',('native',c),v))
   ns.append(total)
  state=ns;ports.append({'round':round_index,'nodes':[round_start,begin+index-1],'before':before,'after':state.copy()})
 assert index==count and next_c-first_c==64*(2*width+width*width)
 return {'width':width,'nodes':[begin,begin+count-1],'count':count,'constants':[first_c,next_c-1],'constant_occurrences':len(consumed),'input_ports':ports[0]['before'],'final_state':state,'round_ports':ports,'node_sha256':hashlib.sha256(json.dumps(records,separators=(',',':')).encode()).hexdigest(),'constant_sha256':hashlib.sha256(json.dumps(consumed,separators=(',',':')).encode()).hexdigest()}

results=[];failures=[];controls=[];source_ids={};anchor_counts={}
for width,file in [(3,'poseidon381.json'),(6,'poseidon381-wide.json')]:
 source=args.runtime/'crates/crypto/primitives/params'/file
 pinned=subprocess.check_output(['git','show','844389ee069e1fb2e576708842d0b389b4d9a44a:crates/crypto/primitives/params/'+file],cwd=args.runtime)
 assert source.read_bytes()==pinned, 'parameter differs from exact runtime Git blob'
 source_ids[file]=digest(source);art=json.loads(source.read_text());assert int(art['modulus'])==p and art['alpha']==5 and art['full_rounds']==8 and art['partial_rounds']==57
 ark=[[int(x,16)for x in row]for row in art['ark']];mds=[[int(x,16)for x in row]for row in art['mds']];assert len(ark)==65 and len(mds)==width and all(len(row)==width for row in ark+mds)
 anchors=con.execute("SELECT n.id FROM nodes n JOIN constants c ON c.id=n.li WHERE n.op='add' AND n.lk=0 AND c.value=? ORDER BY n.id",(f'{ark[1][0]:064x}',)).fetchall();anchor_counts[str(width)]=len(anchors)
 count=7*(width+3*width+2*width*width)+57*(width+3+2*width*width)
 for (begin,)in anchors:
  assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 512*1024**2, 'RSS budget exceeded'
  assert time.monotonic()-start < 120, 'wall budget exceeded'
  try:
   records=con.execute('SELECT id,op,lk,li,rk,ri FROM nodes WHERE id>=? AND id<? ORDER BY id',(begin,begin+count)).fetchall();assert len(records)==count
   first_c=records[0][3];constants_count=64*(2*width+width*width);constants=dict(con.execute('SELECT id,value FROM constants WHERE id>=? AND id<?',(first_c,first_c+constants_count)).fetchall())
   result=match_records(width,begin,ark,mds,records,constants);results.append(result)
   if begin==anchors[0][0]:
    variants=[]
    changed=records.copy();row=list(changed[width]);row[1]='add';changed[width]=tuple(row);variants.append(('square_opcode',changed,constants,ark,mds))
    changed=records.copy();row=list(changed[width]);row[5]+=1;changed[width]=tuple(row);variants.append(('square_operand',changed,constants,ark,mds))
    changed=constants.copy();changed[first_c]=f'{(int(changed[first_c],16)+1)%p:064x}';variants.append(('raw_ARK_constant',records,changed,ark,mds))
    changed=[row.copy()for row in mds];changed[0][0]=(changed[0][0]+1)%p;variants.append(('MDS_parameter',records,constants,ark,changed))
    variants.append(('missing_final_node',records[:-1],constants,ark,mds))
    for name,rs,cs,aks,ms in variants:
     try:match_records(width,begin,aks,ms,rs,cs)
     except AssertionError as e:controls.append({'width':width,'case':name,'same_matcher_rejected':True,'reason':str(e)[:300]})
     else:raise RuntimeError('mutation accepted: '+name)
  except (AssertionError,KeyError,IndexError)as e:failures.append({'width':width,'anchor':begin,'reason':str(e)})
intervals=sorted(x['nodes']for x in results);assert all(a[1]<b[0]for a,b in zip(intervals,intervals[1:]))
assert digest(args.database)==expected
for file,h in source_ids.items():assert digest(args.runtime/'crates/crypto/primitives/params'/file)==h
v={'kind':'exact-source-pattern-census-data-only','runtime_sha':'844389ee069e1fb2e576708842d0b389b4d9a44a','database_sha256':expected,'parameter_sha256':source_ids,'anchor_counts':anchor_counts,'controls':controls,'accepted':len(results),'rejected_candidates':failures,'matched_disjoint_nodes':sum(x['count']for x in results),'matches':results,'limits':['Only rounds1..64 of each candidate permutation are matched; round0,absorption,domain,arity,consumers and runtimecallidentity are not established.','No compilerrowcoverage or Lean/kernel or nativecorrespondence credit.','Exact sourcepattern does not assert these are all runtimehashcalls.'],'elapsed_seconds':time.monotonic()-start,'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'predecessor':'Initial runner failed before DB read because macOS rejected RLIMIT_AS; zero data/proof credit. CPU90s/RSS512MiB-per-block/wall120s now explicit.','full_transfer':'OPEN'}
args.output.write_text(json.dumps(v,indent=2)+'\n');print(json.dumps({k:v[k]for k in ['accepted','anchor_counts','matched_disjoint_nodes','rejected_candidates','elapsed_seconds']}))
