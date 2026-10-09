"""Exact width-three call pattern and phase ports; data only, no proof credit."""
from pathlib import Path
import copy,hashlib,json,resource,sqlite3,subprocess,time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
P=52435875175126190479447740508185965837690552500527637822603658699938581184513
PIN='844389ee069e1fb2e576708842d0b389b4d9a44a'
DATABASE_SHA='da9026b92d643ea8cddaf560b06bc783b291f152f799b48cc836290f57ed9f7d'
BEGIN,END,FIRST_CONSTANT,LAST_CONSTANT=22000,23599,12646,13618
INPUTS=[(2,16577),(2,21951)]
OUTPUT=(2,23593)

def sha(path):
    digest=hashlib.sha256()
    with path.open('rb') as stream:
        while block:=stream.read(1024**2):digest.update(block)
    return digest.hexdigest()

def match(records,constants,ark,mds,inputs=INPUTS,iv=536,expected_output=OUTPUT):
    node,constant=BEGIN,FIRST_CONSTANT
    consumed_nodes=[];consumed_constants=[]
    def merge(operation,left,right):
        nonlocal node,constant
        if left[0]==right[0]=='native':
            return ('native',(left[1]+right[1] if operation=='add' else left[1]*right[1])%P)
        if right[0]=='native':left,right=right,left
        if left[0]=='native':
            assert constants[constant]==left[1],('constant',constant)
            consumed_constants.append([constant,left[1]])
            left=(0,constant);constant+=1
        expected=(operation,*left,*right)
        assert records[node]==expected,('node',node)
        consumed_nodes.append([node,*expected]);node+=1
        return (2,node-1)
    def add(left,right):return merge('add',left,right)
    def mul(left,right):return merge('mul',left,right)
    state=[('native',iv),('native',0),('native',0)]
    for position,word in enumerate(inputs,1):state[position]=add(state[position],word)
    absorbed=state.copy();rounds=[]
    for index in range(65):
        start=node;before=state.copy()
        state=[add(value,('native',coefficient)) for value,coefficient in zip(state,ark[index])]
        after_ark=state.copy()
        for position,value in enumerate(state):
            if index<4 or index>=61 or position==0:
                square=mul(value,value);state[position]=mul(mul(square,square),value)
        after_sbox=state.copy();next_state=[]
        for row in mds:
            total=('native',0)
            for coefficient,value in zip(row,state):total=add(total,mul(('native',coefficient),value))
            next_state.append(total)
        state=next_state
        rounds.append(dict(round=index,nodes_inclusive=[start,node-1],before=before,
            after_ark=after_ark,after_sbox=after_sbox,after_mds=state.copy()))
    assert node==END+1 and constant==LAST_CONSTANT+1
    assert set(records)==set(range(BEGIN,END+1))
    assert set(constants)==set(range(FIRST_CONSTANT,LAST_CONSTANT+1))
    assert state[1]==expected_output,('output',state[1],expected_output)
    return dict(width=3,domain=24,arity=2,iv=iv,input_ports=inputs,
        absorption_nodes_inclusive=[22000,22001],nodes_inclusive=[BEGIN,END],
        node_count=len(consumed_nodes),constants_inclusive=[FIRST_CONSTANT,LAST_CONSTANT],
        constant_count=len(consumed_constants),absorbed_state=absorbed,rounds=rounds,
        final_state=state,result=state[1],
        ordered_matched_node_records_sha256=hashlib.sha256(json.dumps(consumed_nodes,separators=(',',':')).encode()).hexdigest(),
        ordered_matched_constant_records_sha256=hashlib.sha256(json.dumps(consumed_constants,separators=(',',':')).encode()).hexdigest())

def main():
    if not __debug__:raise RuntimeError('optimized Python forbidden')
    resource.setrlimit(resource.RLIMIT_CPU,(60,60))
    start=time.monotonic();self_hash=sha(Path(__file__))
    database=ROOT/'work/parent-full-program/capture/lowering-resume01.sqlite'
    assert sha(database)==DATABASE_SHA
    runtime=ROOT/'work/runtime-snapshot'
    parameter_path='crates/crypto/primitives/params/poseidon381.json'
    parameter=runtime/parameter_path
    raw=subprocess.check_output(['git','show',PIN+':'+parameter_path],cwd=runtime)
    assert raw==parameter.read_bytes()
    artifact=json.loads(raw)
    assert (artifact['schema'],int(artifact['modulus']),artifact['alpha'],artifact['full_rounds'],artifact['partial_rounds'],artifact['skip_matrices'])==('shieldd.poseidon381.v1',P,5,8,57,0)
    ark=[[int(value,16) for value in row]for row in artifact['ark']]
    mds=[[int(value,16) for value in row]for row in artifact['mds']]
    assert len(ark)==65 and len(mds)==3 and all(len(row)==3 for row in ark+mds)
    assert all(0<=value<P for row in ark+mds for value in row)
    db=sqlite3.connect(database.resolve().as_uri()+'?mode=ro',uri=True)
    db.execute('PRAGMA cache_size=-16384')
    records={number:tuple(rest)for number,*rest in db.execute('SELECT id,op,lk,li,rk,ri FROM nodes WHERE id BETWEEN ? AND ? ORDER BY id',(BEGIN,END))}
    constants={number:int(value,16)for number,value in db.execute('SELECT id,value FROM constants WHERE id BETWEEN ? AND ? ORDER BY id',(FIRST_CONSTANT,LAST_CONSTANT))}
    result=match(records,constants,ark,mds)
    variants=[]
    bad=records.copy();old=bad[BEGIN];bad[BEGIN]=('mul',*old[1:]);variants.append(('opcode',bad,constants,ark,mds,INPUTS,536,OUTPUT))
    bad=constants.copy();bad[FIRST_CONSTANT]=(bad[FIRST_CONSTANT]+1)%P;variants.append(('allocated_constant',records,bad,ark,mds,INPUTS,536,OUTPUT))
    bad=copy.deepcopy(ark);bad[0][1]=(bad[0][1]+1)%P;variants.append(('ARK0',records,constants,bad,mds,INPUTS,536,OUTPUT))
    bad=copy.deepcopy(mds);bad[0][0]=(bad[0][0]+1)%P;variants.append(('MDS',records,constants,ark,bad,INPUTS,536,OUTPUT))
    variants.append(('input_swap',records,constants,ark,mds,list(reversed(INPUTS)),536,OUTPUT))
    variants.append(('IV',records,constants,ark,mds,INPUTS,537,OUTPUT))
    bad=records.copy();del bad[END];variants.append(('missing_final_node',bad,constants,ark,mds,INPUTS,536,OUTPUT))
    variants.append(('different_existing_output',records,constants,ark,mds,INPUTS,536,(2,23587)))
    controls=[]
    for name,*arguments in variants:
        try:match(*arguments)
        except (AssertionError,KeyError) as error:controls.append(dict(mutation=name,same_matcher_rejected=True,reason=str(error)))
        else:raise RuntimeError('mutation accepted: '+name)
    assert sha(database)==DATABASE_SHA and sha(Path(__file__))==self_hash and raw==parameter.read_bytes()
    assert time.monotonic()-start<120 and resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<512*1024**2
    result.update(kind='qualified-source-pattern-phase-descriptor-data-only',runtime_sha=PIN,
        database_sha256=DATABASE_SHA,parameter_sha256=hashlib.sha256(raw).hexdigest(),
        matcher_sha256=self_hash,controls=controls,seconds=time.monotonic()-start,
        peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        limits=['Input cuts16577/21951 have no upstream semantic claim.',
                'No actual row coverage, Rust callsite identity, kernel or native refinement credit.'],
        kernel_run=False,proof_credit=0,full_transfer='OPEN')
    destination=HERE/'descriptor01.json';assert not destination.exists()
    destination.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS',result['node_count'],'nodes',result['constant_count'],'constants',len(controls),'controls',result['seconds'],'seconds')

if __name__=='__main__':main()
