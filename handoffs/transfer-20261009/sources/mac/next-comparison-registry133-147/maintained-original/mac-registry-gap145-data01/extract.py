from pathlib import Path
import sqlite3,json,hashlib,sys
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-registry-gap145-data01'
def require(ok,msg):
 if not ok:raise ValueError(msg)
def pin(p):
 b=p.read_bytes();return dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
P=52435875175126190479447740508185965837690552500527637822603658699938581184513;COPY=200692
require(sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode and not sys.flags.optimize,'flags');require(not S.exists(),'fresh');S.mkdir();(S/'extract.py').write_bytes(Path(__file__).read_bytes());db=W/'parent-full-program/capture/lowering-resume01.sqlite';st=db.stat();c=sqlite3.connect('file:'+str(db)+'?mode=ro',uri=True);c.execute('pragma cache_size=-8192');c.execute('pragma query_only=on')
def canon(ts):
 d={}
 for x,v in ts:d[x]=(d.get(x,0)+v)%P
 return [[x,v]for x,v in sorted(d.items())if v]
def scale(k,ts):return canon([[x,k*v]for x,v in ts])
def outline(ts):return sorted([[COPY if x==0 else x,v]for x,v in ts])
ns={r[0]:dict(id=r[0],op=r[1],lk=r[2],li=r[3],rk=r[4],ri=r[5],kind=r[6],terms=json.loads(r[7]),certificate=json.loads(r[8]))for r in c.execute('select id,op,lk,li,rk,ri,kind,terms,certificate from nodes where id between126792 and126802 or id between129115 and129131'.replace('between126792 and126802','between 126792 and 126802').replace('between129115 and129131','between 129115 and 129131'))};require(len(ns)==28,'exact two source gaps')
products={126797:(33774,11036),126800:(33776,11038),129120:(33782,11044),129123:(33784,11046),129126:(33786,11048),129131:(33788,11050)};const={};cuts={};rows=[];entries=[]
def operand(k,i):
 if k==0:
  if i not in const:
   r=c.execute('select value from constants where id=?',(i,)).fetchone();require(r is not None,'const');const[i]=int(r[0],16);require(0<=const[i]<P,'canonical')
  return [[0,const[i]]]if const[i]else[]
 if k==1:return [[3+i,1]]
 require(k==2,'source role')
 if i in ns:return ns[i]['terms']
 r=c.execute('select kind,terms,certificate from nodes where id=?',(i,)).fetchone();require(r is not None and r[0]=='linear','external linear source');cuts[i]=dict(terms=json.loads(r[1]),certificate=json.loads(r[2]));return cuts[i]['terms']
for i,n in ns.items():
 cert=n['certificate'];require(cert['node']==i and cert['left']==[n['lk'],n['li']]and cert['right']==[n['rk'],n['ri']],'operand certificate')
 for k,j in [(n['lk'],n['li']),(n['rk'],n['ri'])]:require(k!=2 or j<i,'backward')
 left=operand(n['lk'],n['li']);right=operand(n['rk'],n['ri']);require(n['kind']=='linear','actual linear')
 if n['op']=='add':require(cert['constructor']=='add'and cert['rows']==[],'add');expected=canon(left+right)
 elif i in products:
  output,rowstart=products[i];require(n['op']=='mul'and cert['constructor']=='product'and cert['rows']==[rowstart,rowstart+1]and cert['auxiliary']==[[output+1,1]],'exact product');expected=[[output,1]]
  entries.append(dict(node=i,left=left,right=right,output=output,auxiliary=output+1,rows=cert['rows']))
  for ix,a,b,role in [(rowstart,canon(left+scale(-1,right)),[[output+1,1]],'minus'),(rowstart+1,canon(left+right),[[output,4],[output+1,1]],'plus')]:
   ra,rb,origin=map(json.loads,c.execute('select a,b,origin from rows where id=?',(ix,)).fetchone());require(ra==a and rb==b and origin==dict(kind='node',id=i,role=role),'exact body/origin');rows.append(dict(index=ix,a=ra,b=rb,outlined_a=outline(ra),outlined_b=outline(rb),origin=origin))
 else:
  require(n['op']=='mul'and cert['rows']==[]and cert['constructor']in['foldedLeft','foldedRight'],'folded');key='lk'if cert['constructor']=='foldedLeft'else'rk';ix='li'if key=='lk'else'ri';require(n[key]==0,'allocated coeff');co=const[n[ix]];require(cert['coefficient']==co,'coeff');expected=scale(co,right if key=='lk'else left)
 require(n['terms']==expected,'LC replay')
r=c.execute('select lk,li,rk,ri,certificate from assertions where id=1467').fetchone();cert=json.loads(r[-1]);require(r[:4]==(0,73384,2,129131)and cert['rows']==[179421]and cert['constructor']=='linear','assertion exact');ra,rb,origin=map(json.loads,c.execute('select a,b,origin from rows where id=179421').fetchone());require(operand(r[0],r[1])==[]and ra==[[33788,P-1]]and rb==[]and origin==dict(kind='assertion',id=1467,role='linear'),'gap refusal body')
require((db.stat().st_size,db.stat().st_mtime_ns)==(st.st_size,st.st_mtime_ns),'DB metadata')
v=dict(entries=entries,arithmetic_rows=rows,assertion=dict(index=179421,a=ra,b=rb,outlined_a=outline(ra),outlined_b=outline(rb),origin=origin,certificate=cert),nodes=ns,external_cuts=cuts,constants=const,runtime='844389ee069e1fb2e576708842d0b389b4d9a44a',database=dict(path=str(db),bytes=st.st_size,mtime_ns=st.st_mtime_ns,historical_sha256='da9026b92d643ea8cddaf560b06bc783b291f152f799b48cc836290f57ed9f7d'),qualification=pin(W/'mac-full-arithmetic45-source01/qualification01.json'),registry=pin(W/'runtime-snapshot/crates/crypto/circuits/src/registry.rs'),range=pin(W/'runtime-snapshot/crates/crypto/circuits/src/range.rs'),scope='DATA only: first/second lexicographic Boolean combination and final unregulated gap refusal. Six captured products12rows plus assertion179421. No assertion1468 or desired truth premise.')
p=S/'selected-data01.json';p.write_text(json.dumps(v,sort_keys=True,separators=(',',':'))+'\n');print(pin(p))
