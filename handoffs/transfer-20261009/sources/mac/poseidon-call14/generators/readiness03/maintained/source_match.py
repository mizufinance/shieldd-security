"""Exact two-permutation forward source matcher, including native folding."""
P=52435875175126190479447740508185965837690552500527637822603658699938581184513
def match(records,constants,ark,mds,inputs,domain,arity,begin):
 assert len(inputs)==arity==6 and len(ark)==65 and len(mds)==6 and all(len(r)==6 for r in ark+mds)
 cursor=begin;ci=min(constants);matched=[];allocated=[];blocks=[]
 def merge(op,left,right):
  nonlocal cursor,ci
  if left[0]==right[0]=='native':return ('native',(left[1]+right[1] if op=='add' else left[1]*right[1])%P)
  if right[0]=='native':left,right=right,left
  if left[0]=='native':
   assert constants[ci]==left[1],('allocated constant',ci);allocated.append([ci,left[1]]);left=(0,ci);ci+=1
  assert records[cursor]==(op,*left,*right),('operation/operands',cursor)
  matched.append([cursor,*records[cursor]]);cursor+=1;return (2,cursor-1)
 add=lambda a,b:merge('add',a,b);mul=lambda a,b:merge('mul',a,b)
 state=[('native',arity*256+domain)]+[('native',0)]*5
 for block,chunk in enumerate([inputs[:5],inputs[5:]]):
  previous=state.copy();start=cursor
  for column,inp in enumerate(chunk,1):state[column]=add(state[column],inp)
  absorption=[start,cursor-1];absorbed=state.copy();rounds=[]
  for ordinal in range(65):
   first=cursor;before=state.copy();state=[add(value,('native',a)) for value,a in zip(state,ark[ordinal])];shifted=state.copy()
   for column,value in enumerate(state):
    if ordinal<4 or ordinal>=61 or column==0:
     sq=mul(value,value);state[column]=mul(mul(sq,sq),value)
   nonlinear=state.copy();state=[]
   for row in mds:
    total=('native',0)
    for coefficient,value in zip(row,nonlinear):total=add(total,mul(('native',coefficient),value))
    state.append(total)
   rounds.append(dict(round=ordinal,nodes=[first,cursor-1],before=before,after_ark=shifted,after_sbox=nonlinear,after=state.copy()))
  blocks.append(dict(block=block,before_absorption=previous,absorption_nodes=absorption,chunk=chunk,absorbed=absorbed,rounds=rounds,after=state.copy()))
 assert set(records)==set(range(begin,cursor));assert set(constants)==set(range(min(constants),ci))
 return dict(domain=domain,arity=arity,IV=arity*256+domain,inputs=inputs,blocks=blocks,final_state=state,result=state[1],matched_nodes=matched,matched_constants=allocated)
