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
entries=[]
for start in [2257,3015]:
 entries.extend([extract(start,False),extract(start+2,True)])
 for window in range(1,126):
  k=start+6+6*(window-1)
  entries.extend([extract(k,False),extract(k+2,False),extract(k+4,True)])
assert len(entries)==754
(root/'entries.json').write_text(json.dumps(entries,separators=(',',':'))+'\n')
print(json.dumps(dict(operations=len(entries),doubles=sum(not e['isAdd'] for e in entries),adds=sum(e['isAdd'] for e in entries),first=entries[0]['assertionStart'],last=entries[-1]['assertionStart'])))
