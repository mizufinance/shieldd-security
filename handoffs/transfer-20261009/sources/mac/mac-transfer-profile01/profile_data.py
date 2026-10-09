"""Disk-backed complete-data size/reuse profile; hash keys give no proof credit."""
import collections,hashlib,json,sqlite3,time
from pathlib import Path
STAGE=Path(__file__).resolve().parent;ROOT=STAGE.parents[1]
OUT=ROOT/'outputs/mac-transfer-profile01';SOURCE=ROOT/'work/parent-full-program/capture/lowering-resume01.sqlite'
def sha(path):
    value=hashlib.sha256()
    with path.open('rb') as stream:
        while raw:=stream.read(1024**2):value.update(raw)
    return value.hexdigest()
started=time.monotonic();provenance=ROOT/'outputs/mac-transfer-pilot01/provenance-successor01.json'
identity=json.loads(provenance.read_text())['inputs']['lowering-resume01.sqlite'];assert sha(SOURCE)==identity['sha256']
source=sqlite3.connect(SOURCE.resolve().as_uri()+'?mode=ro',uri=True)
database=OUT/'profile01.sqlite';assert not database.exists();profile=sqlite3.connect(database)
profile.executescript('PRAGMA journal_mode=OFF; PRAGMA synchronous=OFF; PRAGMA cache_size=-65536; PRAGMA temp_store=FILE; CREATE TABLE pool(hash BLOB PRIMARY KEY,terms INTEGER,bytes INTEGER,occurrences INTEGER); CREATE TABLE templates(hash BLOB PRIMARY KEY,occurrences INTEGER); CREATE TABLE expressions(hash BLOB PRIMARY KEY,occurrences INTEGER); CREATE TABLE nodes(id INTEGER PRIMARY KEY,terms INTEGER,bytes INTEGER);')
counts=collections.Counter();constructors=collections.Counter();histogram=collections.Counter();operand_references=collections.Counter()
nodes=[];pool=[];templates=[];expressions=[];maximum=0;lc_terms=0;lc_bytes=0
def flush():
    profile.executemany('INSERT INTO pool VALUES(?,?,?,1) ON CONFLICT(hash) DO UPDATE SET occurrences=occurrences+1',pool)
    profile.executemany('INSERT INTO templates VALUES(?,1) ON CONFLICT(hash) DO UPDATE SET occurrences=occurrences+1',templates)
    profile.executemany('INSERT INTO expressions VALUES(?,1) ON CONFLICT(hash) DO UPDATE SET occurrences=occurrences+1',expressions)
    profile.executemany('INSERT INTO nodes VALUES(?,?,?)',nodes)
    profile.commit();pool.clear();templates.clear();expressions.clear();nodes.clear()
def lc(raw,category,kind='linear'):
    global maximum,lc_terms,lc_bytes
    terms=json.loads(raw) if isinstance(raw,(bytes,str)) else raw
    assert type(terms) is list and len(terms)<=32768
    canonical=json.dumps(terms,separators=(',',':')).encode()
    maximum=max(maximum,len(terms));lc_terms+=len(terms);lc_bytes+=len(canonical)
    counts[category]+=1;histogram[len(terms)]+=1
    digest=hashlib.sha256(canonical).digest();pool.append((digest,len(terms),len(canonical)))
    expressions.append((hashlib.sha256(kind.encode()+b':'+canonical).digest(),))
    movable=[col for col,value in terms if col not in (0,200692)];origin=min(movable) if movable else 0
    translated=[['constant' if col==0 else 'copy' if col==200692 else col-origin,value] for col,value in terms]
    templates.append((hashlib.sha256(json.dumps(translated,separators=(',',':')).encode()).digest(),))
    if len(pool)>=1000:flush()
    return len(terms),len(canonical)
for i,op,lk,li,rk,ri,kind,terms,certificate in source.execute('SELECT id,op,lk,li,rk,ri,kind,terms,certificate FROM nodes ORDER BY id'):
    length,size=lc(terms,'node_expression',kind);nodes.append((i,length,size))
    constructors[json.loads(certificate)['constructor']]+=1
    operand_references[lk]+=1;operand_references[rk]+=1
    counts['operation_'+op]+=1
for index,a,b in source.execute('SELECT id,a,b FROM rows ORDER BY id'):
    lc(a,'row_side');lc(b,'row_side')
for index,value in source.execute('SELECT id,value FROM constants ORDER BY id'):
    lc([[0,int(value,16)]],'source_constant')
for index in range(22735):lc([[3+index,1]],'source_input')
flush()
unique_lcs,unique_terms,unique_bytes,max_terms=profile.execute('SELECT count(*),sum(terms),sum(bytes),max(terms) FROM pool').fetchone()
unique_expr=profile.execute('SELECT count(*) FROM expressions').fetchone()[0]
translated=profile.execute('SELECT count(*) FROM templates').fetchone()[0]
const_unique=source.execute('SELECT count(DISTINCT value) FROM constants').fetchone()[0]
assertion_constructors=collections.Counter(json.loads(raw)['constructor'] for raw, in source.execute('SELECT certificate FROM assertions'))
# Count operand materialization pressure without duplicating large LC payloads.
profile.execute('ATTACH DATABASE ? AS original',(SOURCE.resolve().as_uri()+'?mode=ro',))
operand_node_terms,operand_node_bytes=profile.execute('SELECT sum(size.terms),sum(size.bytes) FROM (SELECT li AS operand FROM original.nodes WHERE lk=2 UNION ALL SELECT ri AS operand FROM original.nodes WHERE rk=2) AS uses JOIN nodes AS size ON size.id=uses.operand').fetchone()
profile.execute('DETACH DATABASE original')
profile.close()
assert sha(SOURCE)==identity['sha256'],'source DB changed'
result=dict(status='passed',seconds=time.monotonic()-started,source_database=identity,
    complete_source_node_expressions=counts['node_expression'],stored_row_sides=counts['row_side'],
    source_constants=counts['source_constant'],unique_numeric_source_constants=const_unique,
    source_input_lcs=counts['source_input'],total_lc_occurrences=sum(counts[key] for key in ['node_expression','row_side','source_constant','source_input']),
    total_lc_terms=lc_terms,total_canonical_compact_json_lc_bytes=lc_bytes,
    sha_key_unique_lcs=unique_lcs,sha_key_unique_lc_terms=unique_terms,sha_key_unique_lc_bytes=unique_bytes,
    sha_key_unique_expressions_including_kind=unique_expr,
    sha_key_unique_column_translation_templates=translated,
    maximum_lc_terms=maximum,lc_length_histogram=dict(sorted(histogram.items())),
    node_constructor_counts=dict(constructors),assertion_constructor_counts=dict(assertion_constructors),
    raw_operation_counts={key:counts[key] for key in ['operation_add','operation_mul']},
    operand_reference_counts=dict(operand_references),referenced_node_lc_terms_with_duplication=operand_node_terms,
    referenced_node_lc_compact_bytes_with_duplication=operand_node_bytes,
    profile_database_bytes=database.stat().st_size,provenance_receipt_sha256=sha(provenance),
    qualification='SHA-key reuse statistics only; template equivalence, semantic recurrence, canonical exact row coverage remain unproved',
    kernel_run=False,proof_credit=0,full_transfer='OPEN')
target=OUT/'profile-result01.json';assert not target.exists();target.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({key:result[key] for key in ['status','seconds','sha_key_unique_lcs','sha_key_unique_lc_bytes','sha_key_unique_column_translation_templates','maximum_lc_terms','profile_database_bytes']}),flush=True)
