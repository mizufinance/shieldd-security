"""Bounded data comparison only. No kernel or parent-inclusion credit."""
import copy,hashlib,json,pathlib,resource,sqlite3,time
if not __debug__:raise RuntimeError('optimized mode forbidden')
ROOT=pathlib.Path(__file__).resolve().parents[2];OUT=pathlib.Path(__file__).parent
resource.setrlimit(resource.RLIMIT_CPU,(90,90));start=time.monotonic()
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024*1024):h.update(b)
 return h.hexdigest()
def bound():
 assert time.monotonic()-start<120
 assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss<512*1024**2
cp=ROOT/'work/parent-poseidon-census01/result03.json';dp=ROOT/'work/parent-full-program/capture/lowering-resume01.sqlite'
ch=sha(cp);dh=sha(dp);census=json.loads(cp.read_text());assert dh==census['database_sha256']
db=sqlite3.connect(dp.resolve().as_uri()+'?mode=ro',uri=True);db.execute('PRAGMA cache_size=-16384')
def port(ref):
 assert ref[0]==2
 return json.loads(db.execute('SELECT terms FROM nodes WHERE id=?',(ref[1],)).fetchone()[0])
def norm(lc,offset):return [[c if c in [0,200692] else c-offset,v] for c,v in lc]
def extract(match):
 rounds=match['round_ports'][1:];assert [r['round'] for r in rounds]==list(range(2,65))
 initial=[port(ref) for ref in rounds[0]['before']];offset=min(c for lc in initial for c,v in lc if c not in [0,200692])
 rowids=set();result=[]
 for r in rounds:
  ids=sorted({i for cert, in db.execute('SELECT certificate FROM nodes WHERE id BETWEEN ? AND ? ORDER BY id',r['nodes']) for i in json.loads(cert)['rows']})
  assert ids and not rowids.intersection(ids);rowids.update(ids)
  rows=[]
  for i in ids:
   a,b=db.execute('SELECT a,b FROM rows WHERE id=?',(i,)).fetchone();rows.append([norm(json.loads(a),offset),norm(json.loads(b),offset)])
  result.append({'round':r['round'],'before':[norm(port(ref),offset) for ref in r['before']],'after':[norm(port(ref),offset) for ref in r['after']],'rows':rows})
  bound()
 return result,{'width':match['width'],'source_span':match['nodes'],'base_column':offset,'row_count':len(rowids),'row_interval':[min(rowids),max(rowids)],'rounds':[2,64]}
references={};records=[];controls=[]
for match in census['matches']:
 data,record=extract(match);width=match['width']
 if width not in references:
  references[width]=(data,record)
  for label in ['coefficient','column','output_port','missing_row']:
   bad=copy.deepcopy(data)
   if label=='coefficient':bad[0]['rows'][0][0][0][1]+=1
   elif label=='column':bad[0]['rows'][0][0][-1][0]+=1
   elif label=='output_port':bad[-1]['after'][0]=copy.deepcopy(bad[-1]['after'][1])
   else:bad[0]['rows'].pop()
   assert bad!=data;controls.append({'width':width,'mutation':label,'same_comparison_rejects':True})
 reference,ref_record=references[width];assert data==reference,record
 record['column_offset_from_reference']=record['base_column']-ref_record['base_column'];records.append(record)
assert sha(cp)==ch and sha(dp)==dh;bound()
r={'kind':'exact-captured-tail-column-renaming-data-only','runtime_sha':census['runtime_sha'],'database_sha256':dh,'census_sha256':ch,'references':{str(w):r for w,(d,r) in references.items()},'matched':records,'controls':controls,'seconds':time.monotonic()-start,'peak_rss_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'kernel_run':False,'proof_credit':0,'limits':['Exact unoutlined DB rows and before/after ports only.','Rounds 0 and 1, domain/arity/absorption, runtime call identity and global R1CS kernel inclusion OPEN.','Column0 and copy200692 fixed; other columns translated relative to earliest round2 input support.','Width3 reference is a data template, not yet a checked proof template.'],'full_transfer':'OPEN'}
(OUT/'result.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:r[k] for k in ['seconds','peak_rss_bytes','kernel_run']}));print('matched',len(records),'rows',sum(x['row_count'] for x in records))
