from pathlib import Path
import sys,json,hashlib,sqlite3,struct,re
R=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can');S=Path(__file__).resolve().parent
p=52435875175126190479447740508185965837690552500527637822603658699938581184513;COPY=200692

def require(ok,message):
 if not ok:raise ValueError(message)
def pin(path):b=path.read_bytes();return dict(path=str(path),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
def write(path,b):
 if path.exists():require(path.read_bytes()==b,'immutable regeneration '+str(path))
 else:
  with path.open('xb')as f:f.write(b)
def dump(x):return (json.dumps(x,sort_keys=True,separators=(',',':'))+'\n').encode()
def lc(ts):return '['+','.join('('+str(c)+','+str(v)+')'for c,v in ts)+']'
def row(r):return '⟨'+lc(r[0])+','+lc(r[1])+'⟩'
def audited(t,ns):
 names=re.findall(r'^(?:def|theorem) (\w+)',t,re.M)
 return (t+'\n'+''.join('set_option pp.all true in\n#check @ShielddSecurity.'+ns+'.'+n+'\n#print axioms ShielddSecurity.'+ns+'.'+n+'\n'for n in names)).encode()
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'require -I -B -S no -O')
D=S/'selected-data01.json'
if not D.exists():
 db=R/'work/parent-full-program/capture/lowering-resume01.sqlite';con=sqlite3.connect(db.as_uri()+'?mode=ro',uri=True);con.execute('pragma cache_size=-8192');nodes=[29136,29139,29148,29152,29156,29160];products=[]
 def terms(kind,index):
  if kind==1:return [[3+index,1]]
  require(kind==2,'only input/node cuts');r=con.execute('select kind,terms from nodes where id=?',(index,)).fetchone();require(r[0]=='linear','linear input cut');return json.loads(r[1])
 for i,node in enumerate(nodes):
  r=con.execute('select op,lk,li,rk,ri,kind,terms,certificate from nodes where id=?',(node,)).fetchone();c=json.loads(r[7]);require(r[0]=='mul'and r[5]=='linear'and c['constructor']=='product'and c['left']==list(r[1:3])and c['right']==list(r[3:5])and c['rows']==[2722+2*i,2723+2*i],'raw/certificate operation/operand/row agreement');out=json.loads(r[6]);require(out==[[25460+2*i,1]]and c['auxiliary']==[[25461+2*i,1]],'pivot/auxiliary');products.append(dict(node=node,raw=list(r[:6]),certificate=c,left=terms(r[1],r[2]),right=terms(r[3],r[4]),output=out,auxiliary=c['auxiliary']))
 wanted=set(range(2722,2734))|{200769};spool=R/'work/parent-full-program/capture/ordinary01.rows';selected={};digest=hashlib.sha256();nbytes=0
 with spool.open('rb')as f:
  def exact(n):
   global nbytes
   b=f.read(n);require(len(b)==n,'truncated rowspool');digest.update(b);nbytes+=n;return b
  def linear():
   n=struct.unpack('>Q',exact(8))[0];require(n<=32768,'term count');out=[];previous=-1
   for _ in range(n):
    b=exact(36);c=struct.unpack('>I',b[:4])[0];v=int.from_bytes(b[4:],'big');require(previous<c<262144 and 0<v<p,'canonical columns/coefficient');out.append([c,v]);previous=c
   return out
  for i in range(200770):
   a,b=linear(),linear()
   if i in wanted:selected[str(i)]=[a,b]
  require(not f.read(1),'trailing rowspool')
 require(digest.hexdigest()=='5f28e65e804c05828a6cd66515293e28af77a502e4b066f05d162ae33e4ca0c9'and nbytes==86250856,'qualified binary identity')
 originals=[]
 for i in range(2722,2734):
  r=con.execute('select a,b,origin from rows where id=?',(i,)).fetchone();value=[json.loads(r[0]),json.loads(r[1])];outline=[sorted([[COPY if c==0 else c,v]for c,v in ts])for ts in value];require(outline==selected[str(i)],'exact DB/outlined stream bodies');originals.append(dict(index=i,db=value,original=selected[str(i)],origin=json.loads(r[2])))
 outs=[terms(2,n)for n in [29149,29153,29157,29161]];con.close()
 frame=pin(R/'work/parent-full-program/runtime/crates/crypto/circuits/src/tree.rs');shape=pin(R/'work/parent-full-program/capture/ordinary01.shape.json')
 data=dict(runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',historical_db_sha='ef15placeholder',spool=dict(path=str(spool),bytes=nbytes,sha256=digest.hexdigest()),sidecar=shape,primary_source=frame,products=products,rows=originals,copy=selected['200769'],outputs=outs,source_interpretation='tree::root_with_position_bits low/high selection; field polynomial only, no Boolean/assertion proof')
 # Historical DB identity inherited from qualified full census; no fresh3GB hash.
 census=json.loads((R/'work/parent-poseidon-call-census01/qualified01.json').read_bytes());data['historical_db_sha']=census['database_sha256'];data['census']=pin(R/'work/parent-poseidon-call-census01/qualified01.json');write(D,dump(data))
d=json.loads(D.read_bytes());require(d['runtime']=='844389ee069e1fb2e576708842d0b389b4d9a44a','runtime');require(pin(Path(d['primary_source']['path']))==d['primary_source']and pin(Path(d['sidecar']['path']))==d['sidecar'],'source/shape pin')
t='''import ShielddSecurity.RegistryInputJoin24
import ShielddSecurity.CompilerOrder
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.MerkleSelection26Data
open Compiler CompilerCompletion
'''
for i,x in enumerate(d['products']):t+='def left'+str(i)+' : Linear := '+lc(x['left'])+'\ndef right'+str(i)+' : Linear := '+lc(x['right'])+'\ndef step'+str(i)+' : Step := .product left'+str(i)+' right'+str(i)+' [] '+str(25460+2*i)+' '+str(25461+2*i)+'\n'
t+='def materializedSteps : List Step := ['+','.join('step'+str(i)for i in range(6))+']\ndef steps := materializedSteps++[TransferPoseidonCall04Shared01.copyStep]\ndef arithmeticRows : List Row := ['+','.join(row(x['original'])for x in d['rows'])+']\ndef originalRows := arithmeticRows++['+row(d['copy'])+']\ndef outputs : Fin 4 → Linear := fun i => (['+','.join(lc(x)for x in d['outputs'])+'] : List Linear)[i.val]!\ndef left : Fin 6 → Linear := fun i => ([left0,left1,left2,left3,left4,left5] : List Linear)[i.val]!\ndef right : Fin 6 → Linear := fun i => ([right0,right1,right2,right3,right4,right5] : List Linear)[i.val]!\nend ShielddSecurity.MerkleSelection26Data\n'
write(S/'source-root/ShielddSecurity/MerkleSelection26Data.lean',audited(t,'MerkleSelection26Data'))
t=(S/'proof-template.lean.txt').read_text();write(S/'source-root/ShielddSecurity/MerkleSelection26Proof.lean',audited(t,'MerkleSelection26Proof'))
print(json.dumps(dict(data=pin(D),sources={q.name:pin(q)for q in (S/'source-root/ShielddSecurity').iterdir()})))
