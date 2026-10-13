from pathlib import Path
import sqlite3,json,functools
root=Path(__file__).resolve().parent
db=sqlite3.connect('file:'+str(root.parent/'parent-full-program/capture/lowering-resume01.sqlite')+'?mode=ro',uri=True)
db.execute('PRAGMA cache_size=-8192')
p=52435875175126190479447740508185965837690552500527637822603658699938581184513
copy=200692
@functools.lru_cache(None)
def node(ref):
 assert ref[0]==2,ref
 r=db.execute('select op,lk,li,rk,ri,kind,terms,certificate from nodes where id=?',(ref[1],)).fetchone()
 return dict(op=r[0],left=(r[1],r[2]),right=(r[3],r[4]),kind=r[5],terms=json.loads(r[6]),certificate=json.loads(r[7]))
def refs(n):return [n['left'],n['right']]
def unfolded(ref):
 n=node(ref);assert n['op']=='mul'
 assert (n['left'][0]==0)!=(n['right'][0]==0)
 return n['right'] if n['left'][0]==0 else n['left']
def normalized(t):return sorted([[copy if c==0 else c,int(v)] for c,v in t])
def lc(ref):
 if ref[0]==1:return [[ref[1]+3,1]]
 if ref[0]==0:
  v=int(db.execute('select value from constants where id=?',(ref[1],)).fetchone()[0],16)
  return [[copy,v]] if v else []
 n=node(ref);assert n['kind']=='linear',(ref,n['kind']);return normalized(n['terms'])
def rawrow(i):
 a,b=db.execute('select a,b from rows where id=?',(i,)).fetchone();return [normalized(json.loads(a)),normalized(json.loads(b))]
def assertion(i):
 a=db.execute('select lk,li,rk,ri from assertions where id=?',(i,)).fetchone();return (a[0],a[1]),(a[2],a[3])
def extract(pos,isadd):
 xp,cross=assertion(pos);yp,ysum=assertion(pos+1)
 nx=node(xp);ny=node(yp);cr=node(cross);part=node(cr['left'])
 sumref=part['left'];xxref=unfolded(part['right']);yyref=unfolded(cr['right'])
 xx=node(xxref);yy=node(yyref)
 selected=[xxref,yyref,sumref]
 if isadd:
  dx=node(nx['right']);dt=dx['right'] if dx['left'][0]==0 else dx['left'];delta=unfolded(dt);selected+=[delta]
  ports=[[[copy,1]],lc(xx['left']),lc(yy['left']),lc(xx['right']),lc(yy['right']),lc(nx['left']),lc(ny['left']),lc(xxref),normalized(xx['certificate']['auxiliary']),lc(yyref),normalized(yy['certificate']['auxiliary']),lc(sumref),normalized(node(sumref)['certificate']['auxiliary']),lc(delta),normalized(node(delta)['certificate']['auxiliary']),lc(xp),normalized(nx['certificate']['auxiliary']),lc(yp),normalized(ny['certificate']['auxiliary'])]
 else:
  assert xx['left']==xx['right'] and yy['left']==yy['right']
  ports=[[[copy,1]],lc(xx['left']),lc(yy['left']),lc(nx['left']),lc(ny['left']),lc(xxref),lc(yyref),lc(sumref),lc(xp),normalized(nx['certificate']['auxiliary']),lc(yp),normalized(ny['certificate']['auxiliary'])]
 selected += [xp,yp]
 arithmetic=sorted(set(i for ref in selected for i in node(ref)['certificate']['rows']))
 assert len(arithmetic)==(12 if isadd else 7),(pos,arithmetic)
 assert arithmetic==list(range(arithmetic[0],arithmetic[-1]+1)),pos
 return dict(isAdd=isadd,ports=ports,arithmeticStart=arithmetic[0],arithmeticRows=[rawrow(i) for i in arithmetic],assertionStart=pos,assertionRows=[rawrow(177954+pos),rawrow(177955+pos)])

def ancestors(ref):
 seen=set(); todo=[ref]
 while todo:
  r=todo.pop()
  if r[0]!=2 or r in seen:continue
  seen.add(r);todo.extend(refs(node(r)))
 return seen

def selector(xref,yref,low,high,base,twice,triple):
 products=[]
 for ref in [xref,yref]:
  candidates=[r for r in ancestors(ref) if node(r)['op']=='mul' and node(r)['left']==(1,high-3) and node(r)['certificate'].get('constructor')=='product' and any(c in {j for j,v in lc(ref)} for c,v in lc(r))]
  assert len(candidates)==1,(ref,candidates)
  h=candidates[0];yes=node(node(h)['right'])['left'];a=node(yes)['right']
  no=unfolded(node(node(h)['right'])['right']);b=node(no)['right']
  assert node(a)['left']==(1,low-3) and node(b)['left']==(1,low-3)
  products.extend([a,b,h])
 ports=[[[copy,1]],[[low,1]],[[high,1]]]+[[[i,1]] for i in base+twice+triple]
 for r in products:ports.extend([lc(r),normalized(node(r)['certificate']['auxiliary'])])
 ar=sorted(set(i for r in products for i in node(r)['certificate']['rows']))
 assert len(ar)==12 and ar==list(range(ar[0],ar[0]+12))
 return dict(ports=ports,arithmeticStart=ar[0],arithmeticRows=[rawrow(i) for i in ar],outputX=lc(xref),outputY=lc(yref))
entries=[]
for start,base,twice,triple in [(2257,[1504,1505],[2253,2254],[2255,2256]),(3015,[1520,1521],[3009,3010],[3011,3012])]:
 for w in range(126):
  if w==0:
   xr=assertion(start+4)[1];yr=assertion(start+5)[1]
  else:
   pos=start+10+6*(w-1)
   xp,cross=assertion(pos);cr=node(cross);part=node(cr['left']);xx=node(unfolded(part['right']));yy=node(unfolded(cr['right']))
   xr=xx['right'];yr=yy['right']
  e=selector(xr,yr,2250-2*w,2251-2*w,base,twice,triple)
  e['familyStart']=start;e['window']=w;entries.append(e)
assert len(entries)==252
(root/'entries.json').write_text(json.dumps(entries,separators=(',',':'))+'\n')
print(json.dumps(dict(selectors=len(entries),first=entries[0]['arithmeticStart'],last=entries[-1]['arithmeticStart'])))
