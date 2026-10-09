"""Exact two-round source matcher: native folding and constant-first Var merge."""
P=52435875175126190479447740508185965837690552500527637822603658699938581184513
def match(records,constants,ark,mds,inputs,domain,arity,begin):
 assert arity==len(inputs) and len(mds)==3 and all(len(row)==3 for row in ark+mds)
 cursor=begin;constant=min(constants);matched=[];allocated=[]
 def merge(op,left,right):
  nonlocal cursor,constant
  if left[0]==right[0]=='native':return ('native',(left[1]+right[1] if op=='add' else left[1]*right[1])%P)
  if right[0]=='native':left,right=right,left
  if left[0]=='native':
   assert constants[constant]==left[1],('allocated constant',constant)
   allocated.append([constant,left[1]]);left=(0,constant);constant+=1
  actual=(op,*left,*right);assert records[cursor]==actual,('operation/operands',cursor)
  matched.append([cursor,*actual]);cursor+=1;return (2,cursor-1)
 add=lambda x,y:merge('add',x,y);mul=lambda x,y:merge('mul',x,y)
 state=[('native',arity*256+domain),('native',0),('native',0)]
 for index,input in enumerate(inputs,1):state[index]=add(state[index],input)
 absorbed=state.copy();rounds=[]
 for ordinal in range(2):
  first=cursor;before=state.copy();state=[add(v,('native',a)) for v,a in zip(state,ark[ordinal])];shifted=state.copy()
  for column,value in enumerate(state):
   square=mul(value,value);state[column]=mul(mul(square,square),value)
  transformed=state.copy();state=[('native',0)]*3
  for i,row in enumerate(mds):
   for a,v in zip(row,transformed):state[i]=add(state[i],mul(('native',a),v))
  rounds.append(dict(round=ordinal,nodes_inclusive=[first,cursor-1],before=before,after_ark=shifted,after_sbox=transformed,after_mds=state.copy()))
 assert set(records)==set(range(begin,cursor));assert set(constants)==set(range(min(constants),constant));assert len(matched)==len(records)
 return dict(width=3,domain=domain,arity=arity,IV=arity*256+domain,input_ports=inputs,absorbed_state=absorbed,rounds=rounds,nodes=[begin,cursor-1],matched_nodes=matched,matched_constants=allocated)
