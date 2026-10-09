"""Independent recursive certificate arithmetic check; never counts as Lean primality evidence."""
import pathlib,json,hashlib,math,copy,time
if not __debug__:raise RuntimeError('optimized mode forbidden')
P=pathlib.Path(__file__).parent;root=6554484396890773809930967563523245729705921265872317281365359162392183254199

def check(data):
 assert data['subgroup_order']==root
 entries=data['certificates'];assert entries and str(root)in entries;done=set()
 for key in sorted(entries,key=int):
  n=int(key);x=entries[key];assert x['n']==n and n>1 and 0<x['base']<n
  factors=x['factors'];assert all(isinstance(q,int) and q in done and q<n for q in factors)
  assert math.prod(factors)==n-1
  assert pow(x['base'],n-1,n)==1
  records=x['residues'];assert len(records)==len({z['q']for z in records})
  assert {z['q']for z in records}==set(factors)
  for z in records:
   q=z['q'];assert z['exponent']==(n-1)//q and 0<=z['residue']<n
   assert pow(x['base'],z['exponent'],n)==z['residue']!=1
  done.add(n)
 assert root in done and data['root_factorization']==entries[str(root)]['factors']
 return len(done)
start=time.monotonic();file=P/'candidate.json';data=json.loads(file.read_text());count=check(data);controls=[]
for case in ['base','residue','factor_omission','exponent','missing_child','cycle']:
 x=copy.deepcopy(data);top=x['certificates'][str(root)]
 if case=='base':top['base']=2
 elif case=='residue':top['residues'][0]['residue']=(top['residues'][0]['residue']+1)%root
 elif case=='factor_omission':top['factors'].pop()
 elif case=='exponent':top['residues'][0]['exponent']+=1
 elif case=='missing_child':del x['certificates'][str(top['factors'][-1])]
 else:top['factors'][0]=root
 try:check(x)
 except AssertionError:controls.append({'mutation':case,'same_validator_rejected':True})
 else:raise RuntimeError('mutation accepted '+case)
result={'kind':'independent-recursive-Lucas-candidate-arithmetic-validation','candidate_sha256':hashlib.sha256(file.read_bytes()).hexdigest(),'nodes':count,'controls':controls,'root_factorization_product':math.prod(data['root_factorization']),'seconds':time.monotonic()-start,'kernel_run':False,'primality_credit':0,'full_transfer':'OPEN'};(P/'validation.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS',count,'nodes',len(controls),'controls')
