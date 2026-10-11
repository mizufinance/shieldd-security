"""Independent bounded readonly node/row/certificate replay and signed comparison recipes."""
from pathlib import Path
import hashlib,json,sqlite3,subprocess
J=Path(__file__).parent;W=J.parent
P=52435875175126190479447740508185965837690552500527637822603658699938581184513
sha=lambda b:hashlib.sha256(b).hexdigest()
def canon(ts):
 d={}
 for k,v in ts:d[k]=(d.get(k,0)+v)%P
 return [[k,v]for k,v in sorted(d.items())if v]
def scale(k,ts):return canon([[x,k*v]for x,v in ts])
def outline(ts):return sorted([[200692 if x==0 else x,v]for x,v in ts])
tasks=[('next-high-limb133','mac-next-high-limb133-data01'),('next-high-zero137','mac-next-high-zero137-data01'),('next-low-limb140','mac-next-low-limb140-data01'),('registry-gap145','mac-registry-gap145-data01')]
for label,folder in tasks:
 D=J/(label+'-data-review01');D.mkdir();S=W/folder;raw=(S/'selected-data01.json').read_bytes();q=json.loads(raw);R=D/'extraction-replay01';R.mkdir();original=(S/'extract.py').read_bytes();(R/'extract-original.py').write_bytes(original)
 t=original.decode()
 if label=='registry-gap145':
  old="W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-registry-gap145-data01'";assert t.count(old)==1
  t=t.replace(old,'W=Path('+repr(str(W))+');S=Path('+repr(str(R/'isolated-output'))+')');output=R/'isolated-output/selected-data01.json'
 else:
  old='S=Path(__file__).resolve().parent;W=S.parent;';assert t.count(old)==1;t=t.replace(old,'S=Path(__file__).resolve().parent;W=Path('+repr(str(W))+');');output=R/'selected-data01.json'
 (R/'extract-replay.py').write_text(t);run=subprocess.run(['python3','-I','-B','-S',str(R/'extract-replay.py')],capture_output=True,timeout=60);assert run.returncode==0,run.stderr;assert output.read_bytes()==raw
 db=Path(q['database']['path']);before=(db.stat().st_size,db.stat().st_mtime_ns);assert before==(q['database']['bytes'],q['database']['mtime_ns']);c=sqlite3.connect(db.as_uri()+'?mode=ro&immutable=1',uri=True);c.execute('pragma cache_size=-8192');c.execute('pragma query_only=on')
 query='SELECT id,op,lk,li,rk,ri,kind,terms,certificate FROM nodes WHERE '
 if label=='registry-gap145':query+='id BETWEEN126792 AND126802 OR id BETWEEN129115 AND129131';query=query.replace('BETWEEN126','BETWEEN 126').replace('BETWEEN129','BETWEEN 129').replace('AND126','AND 126').replace('AND129','AND 129');args=[]
 else:query+='id BETWEEN ? AND ?';args=q['source_span']
 nodes={r[0]:dict(id=r[0],op=r[1],lk=r[2],li=r[3],rk=r[4],ri=r[5],kind=r[6],terms=json.loads(r[7]),certificate=json.loads(r[8]))for r in c.execute(query,args)}
 if label=='registry-gap145':assert len(nodes)==28 and {str(k):v for k,v in nodes.items()}==q['nodes']
 else:assert len(nodes)==q['source_nodes'] and sha(json.dumps(nodes,sort_keys=True,separators=(',',':')).encode())==q['source_node_lc_sha256']
 constants={int(k):v for k,v in q['constants'].items()}
 for k,v in constants.items():assert int(c.execute('SELECT value FROM constants WHERE id=?',(k,)).fetchone()[0],16)==v and 0<=v<P
 cuts={int(k):v for k,v in q.get('external_cuts',{}).items()}
 for k,v in cuts.items():
  r=c.execute('SELECT kind,terms,certificate FROM nodes WHERE id=?',(k,)).fetchone();assert r[0]=='linear' and json.loads(r[1])==v['terms'] and json.loads(r[2])==v['certificate']
 def operand(k,i):
  if k==0:return [[0,constants[i]]]if constants[i]else[]
  if k==1:return [[3+i,1]]
  assert k==2
  if i in nodes:assert nodes[i]['kind']=='linear';return nodes[i]['terms']
  return cuts[i]['terms']
 arithmetic=[]
 for i,n in sorted(nodes.items()):
  cert=n['certificate'];assert cert['node']==i and cert['left']==[n['lk'],n['li']] and cert['right']==[n['rk'],n['ri']]
  assert all(k!=2 or j<i for k,j in [(n['lk'],n['li']),(n['rk'],n['ri'])]);left=operand(n['lk'],n['li']);right=operand(n['rk'],n['ri']);kind=cert['constructor']
  if kind=='add':assert n['op']=='add' and n['kind']=='linear' and cert['rows']==[];expected=canon(left+right)
  elif kind=='deferred':assert n['op']=='mul' and n['kind']=='square' and left==right and cert['rows']==[];expected=left
  elif kind in ['foldedLeft','foldedRight']:
   k='lk'if kind=='foldedLeft'else'rk';ix='li'if k=='lk'else'ri';assert n[k]==0 and n['op']=='mul' and n['kind']=='linear' and cert['rows']==[];co=constants[n[ix]];assert cert['coefficient']==co;expected=scale(co,right if k=='lk'else left)
  else:
   assert kind=='product' and n['op']=='mul' and n['kind']=='linear';assert len(n['terms'])==1 and n['terms'][0][1]==1;expected=n['terms'];aux=cert['auxiliary'];assert aux==[[expected[0][0]+1,1]]
   for index,a,b,role in [(cert['rows'][0],canon(left+scale(-1,right)),aux,'minus'),(cert['rows'][1],canon(left+right),canon(aux+scale(4,expected)),'plus')]:
    aa,bb,origin=map(json.loads,c.execute('SELECT a,b,origin FROM rows WHERE id=?',(index,)).fetchone());assert (aa,bb,origin)==(a,b,dict(kind='node',id=i,role=role));arithmetic.append(dict(index=index,a=a,b=b,outlined_a=outline(a),outlined_b=outline(b),origin=origin))
  assert expected==n['terms']
 assert arithmetic==q.get('arithmetic_rows',[])
 if label=='next-high-limb133':
  assert q['borrow']==1242 and q['difference']==1243 and q['bits']==[1244,1371];assert nodes[127056]['terms']==[[854+i,2**i]for i in range(127)] and nodes[127310]['terms']==[[599+i,2**i]for i in range(127)];width=127;borrow=1242;diff=1243;bits=1244;positive=599;negative=854;first=179157
 elif label=='next-low-limb140':
  assert q['borrow']==1373 and q['difference']==1374 and q['bits']==[1375,1503];assert nodes[128468]['terms']==[[726+i,2**i]for i in range(128)] and nodes[128724]['terms']==[[471+i,2**i]for i in range(128)];width=128;borrow=1373;diff=1374;bits=1375;positive=471;negative=726;first=179290
 if label in ['next-high-limb133','next-low-limb140']:
  recipes=[([[borrow if j==0 else diff+j,1]],[[borrow if j==0 else diff+j,1]])for j in range(width+1)]
  recipes += [(canon([[diff,-1]]+[[bits+i,2**i]for i in range(width)]),[]),(canon([[positive+i,2**i]for i in range(width)]+[[negative+i,-2**i]for i in range(width)]+[[borrow,2**width],[diff,-1]]),[])];rows=q['rows']
 elif label=='next-high-zero137':
  delta=canon([[854+i,2**i]for i in range(127)]+[[599+i,-2**i]for i in range(127)]);assert delta==q['delta']==nodes[128207]['terms'];assert q['zero']==1371 and q['inverse']==1372 and q['write_window']==[1371,1373];assert [x['index']for x in arithmetic]==list(range(11040,11044));recipes=[([[1371,1]],[[1371,1]]),(canon([[33778,1],[1371,1],[0,-1]]),[]),([[33780,P-1]],[])];first=179287;rows=q['rows']
 else:
  assert [(e['node'],e['output'],e['rows'])for e in q['entries']]==[(126797,33774,[11036,11037]),(126800,33776,[11038,11039]),(129120,33782,[11044,11045]),(129123,33784,[11046,11047]),(129126,33786,[11048,11049]),(129131,33788,[11050,11051])];recipes=[([[33788,P-1]],[])];first=179421;rows=[q['assertion']]
 assert len(rows)==len(recipes)
 for offset,(a,b)in enumerate(recipes):
  index=first+offset;entry=rows[offset];assert entry['index']==index;aa,bb,origin=map(json.loads,c.execute('SELECT a,b,origin FROM rows WHERE id=?',(index,)).fetchone());assert aa==a==entry['a'] and bb==b==entry['b'];assert entry['outlined_a']==outline(a) and entry['outlined_b']==outline(b);assert origin==entry['origin'];assert origin['kind']=='assertion' and origin['id']==index-177954
  ar=c.execute('SELECT lk,li,rk,ri,certificate FROM assertions WHERE id=?',(index-177954,)).fetchone();cert=json.loads(ar[4]);assert cert==entry['certificate'] and cert['left']==list(ar[:2]) and cert['right']==list(ar[2:4]) and cert['rows']==[index]
 for key in ['binary_qualification','range_source','registry_source','qualification','range','registry']:
  if key in q:
   pin=q[key];b=Path(pin['path']).read_bytes();assert len(b)==pin['bytes'] and sha(b)==pin['sha256']
 c.close();assert before==(db.stat().st_size,db.stat().st_mtime_ns)
 report=dict(status='PASSED',kind='Exact original extraction and independent readonly node/row/certificate replay with signed comparison recipes; DATA only',selected_data_sha256=sha(raw),original_extract_sha256=sha(original),raw_nodes=len(nodes),constants=len(constants),actual_assertion_rows=len(recipes),actual_arithmetic_rows=len(arithmetic),positions=[first,first+len(recipes)-1],database_metadata_preserved=True,replay_delta='Only output placement; original DB/source/data pins unchanged',full_transfer='OPEN',native_correspondence='OPEN');(D/'data-review01.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report))
