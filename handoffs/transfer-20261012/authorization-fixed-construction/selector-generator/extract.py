from pathlib import Path
import sqlite3,json,hashlib
P=52435875175126190479447740508185965837690552500527637822603658699938581184513;COPY=200692;D=(-10240*pow(10241,-1,P))%P
c=sqlite3.connect('file:work/parent-full-program/capture/lowering-resume01.sqlite?mode=ro',uri=True);c.execute('PRAGMA cache_size=-8192')
ops=json.load(open('work/mac-authorization-fixed-capture479-source01/entries.json'))
def outlined(t):return sorted([[COPY if i==0 else i,v] for i,v in t])
def rows(start):return [[outlined(json.loads(a)),outlined(json.loads(b))] for a,b in c.execute('select a,b from rows where id>=? and id<? order by id',(start,start+4))]
def add(a,b):
 x,y=a;u,v=b;delta=D*x*u*y*v%P
 return [(x*v+y*u)*pow((1+delta)%P,-1,P)%P,(y*v+x*u)*pow((1-delta)%P,-1,P)%P]
def curve(a):
 x,y=a;return (-x*x+y*y-1-D*x*x*y*y)%P==0
items=[]
for i in range(126):
 low=3767+2*i;high=low+1;start=39698 if i==0 else ops[i-1]['arithmeticStart']-4;r=rows(start)
 if i==0:
  selected=[[[low,4139425550610461525665941076812662132363359224232624900223172373014329534291],[62436,1]],[[COPY,1],[low,39635691377166599497441725607757882405510648532010642268690928210480481875247],[62438,1]]]
 else:selected=ops[i-1]['ports'][3:5]
 sx,sy=map(dict,selected);base=[sx[low],(sy[low]+1)%P];plusx=dict(r[1][0]);plusy=dict(r[3][0]);assert plusx[high]==plusy[high]==1
 twice=[plusx[COPY],(plusy[COPY]+1)%P];triple=[(plusx[low]+base[0]+twice[0])%P,(plusy[low]+base[1]+twice[1]-1)%P]
 assert curve(base) and twice==add(base,base) and triple==add(twice,base),i
 if items:assert base==add(items[-1]['twice'],items[-1]['twice']),i
 items.append(dict(index=i,low=low,high=high,base=base,twice=twice,triple=triple,next=add(twice,twice),arithmeticStart=start,arithmeticRows=r,selected=selected,outputColumn=4019+2*i))
out=Path('work/mac-authorization-fixed-table480-source01');out.mkdir(exist_ok=True);(out/'table.json').write_text(json.dumps(items,indent=2)+'\n');print(json.dumps(dict(status='source-pattern extraction, not kernel proof',windows=len(items),base=items[0]['base'],last=items[-1]['outputColumn'])))
