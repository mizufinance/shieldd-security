"""Extend the actual exclusion slice with Boolean and annihilator rows.

The original guard extractor and all queued packets stay unchanged. This
additional complete replay checks the is_zero construction's other equations
and the sixteen actual unit write pivots. No witness values propose rows.
"""
from . import transfer_encryption_registered_guard as guard
from . import transfer_arithmetic as arithmetic, transfer_relation as relation
from .transfer_balance_rows import canonical,combine


def _annihilator(value,zero,normalized):
    matches = []
    for output,product in guard._product_outputs(value,zero,normalized):
        assertions = [i for i,(a,b) in normalized.items() if not b and
            a in (output,canonical((c,-v) for c,v in output))]
        if len(assertions) == 1:
            matches.append(dict(output=output,product=product,assertion=assertions[0]))
    if len(matches) != 1:
        raise relation.RelationError('registered completion one annihilator product/assertion required')
    return matches[0]


def extract(checked,open_stream,guard_extracted):
    raw,_,point,flag,c = guard.recheck(checked,guard_extracted)
    obj = checked['metadata']
    selected = set(raw)
    wanted = set(selected)
    for axis in ('x','y'):
        for index in c[axis]['rows']:
            wanted.update(range(max(0,index-32),min(obj['full_rows'],index+33)))
    if len(wanted) > 8192:
        raise relation.RelationError('registered completion neighborhood8192 bound')
    records = {}
    def observe(row):
        if row['row'] in wanted:
            records[row['row']] = row
    with open_stream() as stream:
        identity = relation.inspect(stream,obj['relation_digest'],observe)
    if identity != guard_extracted['identity']:
        raise relation.RelationError('registered completion complete replay identity mismatch')
    copy = obj['constant_copy']
    normalized = {i:tuple(canonical((0 if col == copy else col,int(v,16)) for col,v in row[key])
                    for key in ('a','b')) for i,row in records.items()}
    for i,row in raw.items():
        if records.get(i) != next(r for r in guard_extracted['selected_rows'] if r['row'] == i):
            raise relation.RelationError('registered completion original guard row changed')
    extra = {}
    for axis,operand in (('x',point[0]),('y',combine(point[1],guard.ONE,-1))):
        zero = c['zero_'+axis]
        booleans = [i for i,row in normalized.items() if row == (zero,zero)]
        if len(booleans) != 1:
            raise relation.RelationError('registered completion unique zero Boolean row required')
        annihilator = _annihilator(operand,zero,normalized)
        extra[axis] = dict(boolean=booleans[0],annihilator=annihilator)
        selected.add(booleans[0])
        selected.update(annihilator['product']['rows'])
        selected.add(annihilator['assertion'])
    writes = {}
    def write(name,lc):
        if not guard._unit(lc):
            raise relation.RelationError('registered completion actual unit write pivot required')
        writes[name] = lc[0][0]
    for axis in ('x','y'):
        for field in ('zero_','inverse_'):
            write(field+axis,c[field+axis])
        write('reciprocal_output_'+axis,c[axis]['output'])
        write('reciprocal_auxiliary_'+axis,c[axis]['auxiliary'])
        write('annihilator_output_'+axis,extra[axis]['annihilator']['output'])
        write('annihilator_auxiliary_'+axis,extra[axis]['annihilator']['product']['auxiliary'])
    for key in ('equal','forbidden'):
        write(key,c[key])
        write(key+'_auxiliary',c[key+'_certificate']['auxiliary'])
    input_columns = {0,copy,*[lc[0][0] for lc in (*point,flag)]}
    if len(writes) != 16 or len(set(writes.values())) != 16 or set(writes.values()) & input_columns:
        raise relation.RelationError('registered completion sixteen distinct fresh writes required')
    if len(selected) != 20:
        raise relation.RelationError('registered completion twenty distinct actual rows required')
    return dict(identity=identity,metadata_sha256=checked['metadata_sha256'],
        guard=guard_extracted,extra=extra,writes=writes,input_columns=sorted(input_columns),
        selected_rows=[records[i] for i in sorted(selected)],
        scope='Actual twenty-row registered identity-exclusion construction slice and sixteen '
              'write pivots; algebraic construction and preserved outside columns must be '
              'proved in Lean. Surrounding full Transfer legality/ownership remain OPEN')


def recheck(checked,extracted):
    raw,normalized = arithmetic.normalize_selection(extracted,checked['metadata'],checked['metadata_sha256'])
    guard_raw,_,point,flag,c = guard.recheck(checked,extracted['guard'])
    if any(raw.get(i) != row for i,row in guard_raw.items()):
        raise relation.RelationError('registered completion guard row transport changed')
    expected_writes = {}
    def put(name,lc):
        if not guard._unit(lc):
            raise relation.RelationError('registered completion unit pivot required')
        expected_writes[name] = lc[0][0]
    used = set(guard_raw)
    for axis,operand in (('x',point[0]),('y',combine(point[1],guard.ONE,-1))):
        extra = extracted['extra'][axis]
        zero = c['zero_'+axis]
        if normalized.get(extra['boolean']) != (zero,zero):
            raise relation.RelationError('registered completion zero Boolean certificate changed')
        actual = _annihilator(operand,zero,normalized)
        # JSON containers are immaterial; every coefficient and row remains exact.
        import json
        if json.dumps(actual,sort_keys=True) != json.dumps(extra['annihilator'],sort_keys=True):
            raise relation.RelationError('registered completion annihilator certificate changed')
        used.add(extra['boolean'])
        used.update(actual['product']['rows'])
        used.add(actual['assertion'])
        for field in ('zero_','inverse_'):
            put(field+axis,c[field+axis])
        put('reciprocal_output_'+axis,c[axis]['output'])
        put('reciprocal_auxiliary_'+axis,c[axis]['auxiliary'])
        put('annihilator_output_'+axis,actual['output'])
        put('annihilator_auxiliary_'+axis,actual['product']['auxiliary'])
    for key in ('equal','forbidden'):
        put(key,c[key])
        put(key+'_auxiliary',c[key+'_certificate']['auxiliary'])
    input_columns = {0,checked['metadata']['constant_copy'],*[lc[0][0] for lc in (*point,flag)]}
    if (extracted['writes'] != expected_writes or len(set(expected_writes.values())) != 16 or
            set(expected_writes.values()) & input_columns or sorted(input_columns) != extracted['input_columns'] or
            used != set(raw) or len(raw) != 20):
        raise relation.RelationError('registered completion complete row/write ownership changed')
    return raw,normalized,point,flag,c,expected_writes
