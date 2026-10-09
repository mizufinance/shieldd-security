"""Recover the registered payload identity exclusion from actual squared rows.

Two complete digest checks propose only bounded physical neighborhoods. Exact
reciprocal and conjunction certificates supply the semantics; source labels,
honest values and hashes do not supply a nonidentity premise.
"""
from . import transfer_relation as relation, transfer_arithmetic as arithmetic
from .transfer_balance_rows import canonical, combine
from .transfer_encryption_dh_keys import infer_regulated_selectors

ONE = ((0, 1),)


def _unit(lc):
    return len(lc) == 1 and lc[0][0] > 2 and lc[0][1] == 1


def _boundary(checked):
    obj = checked.get('metadata', {})
    if (checked.get('qualified') is not True or
            obj.get('schema') != 'shieldd-transfer-encryption-dh-v1' or
            type(obj.get('role')) is not int or obj['role'] != 0):
        raise relation.RelationError('registered guard qualified first DH occurrence required')
    inferred = infer_regulated_selectors(checked)
    def actual(value):
        return (checked['derived'][value[1]] if value[0] == 'source'
                else canonical([(0, value[1])]))
    point = tuple(actual(v) for v in inferred['selectors']['payload_key']['leaf'])
    flag = actual(inferred['regulated_candidate'])
    if not all(_unit(v) for v in (*point, flag)) or len({v[0][0] for v in (*point, flag)}) != 3:
        raise relation.RelationError('registered guard distinct actual leaf and regulated witnesses required')
    return obj, point, flag


def _product_outputs(left, right, normalized):
    """Recover actual products, then independently recheck their two rows."""
    plus = combine(left, right)
    minus = combine(left, right, -1)
    negative = canonical((c, -v) for c, v in minus)
    results = {}
    first = [(i, b) for i, (a, b) in normalized.items() if a in (minus, negative)]
    second = [(i, b) for i, (a, b) in normalized.items() if a == plus]
    for i, a in first:
        for j, b in second:
            output = canonical((c, v * pow(4, -1, relation.MODULUS))
                               for c, v in combine(b, a, -1))
            if _unit(output) and i != j:
                cert = arithmetic.product_certificate(left, right, output, normalized)
                results[output] = cert
    return sorted(results.items())


def extract(checked, open_stream):
    obj, point, flag = _boundary(checked)
    operands = (point[0], combine(point[1], ONE, -1))
    copy = obj['constant_copy']
    raw_link = (canonical([(0, 1), (copy, -1)]), ())
    links, candidates = [], [set(), set()]
    def normalize(row):
        return tuple(canonical((0 if c == copy else c, int(v, 16)) for c, v in row[k])
                     for k in ('a', 'b'))
    def observe_first(row):
        raw = tuple(tuple((c, int(v, 16)) for c, v in row[k]) for k in ('a', 'b'))
        if raw == raw_link:
            links.append(row['row'])
        a, b = normalize(row)
        if not _unit(b):
            return
        for axis, operand in enumerate(operands):
            for inverse in (combine(operand, a), combine(operand, a, -1)):
                if _unit(inverse) and inverse[0][0] not in {c for c, _ in operand}:
                    candidates[axis].add((inverse, row['row']))
                    if len(candidates[axis]) > 64:
                        raise relation.RelationError('registered guard inverse candidate64 bound')
    with open_stream() as stream:
        first = relation.inspect(stream, obj['relation_digest'], observe_first)
    if (first['domain_size'] != obj['domain_size'] or first['stored_rows'] != obj['full_rows'] or
            len(links) != 1 or not all(candidates)):
        raise relation.RelationError('registered guard complete shape, unique link and inverses required')
    wanted = set(links)
    for axis in candidates:
        for _, index in axis:
            wanted.update(range(max(0, index-32), min(obj['full_rows'], index+33)))
            if len(wanted) > 8192:
                raise relation.RelationError('registered guard neighborhood8192 bound')
    records = {}
    def observe_second(row):
        if row['row'] in wanted:
            records[row['row']] = row
    with open_stream() as stream:
        second = relation.inspect(stream, obj['relation_digest'], observe_second)
    if first != second:
        raise relation.RelationError('registered guard two complete replay identities differ')
    normalized = {i: normalize(row) for i, row in records.items()}
    axis_matches = []
    for axis, operand in enumerate(operands):
        matches = {}
        for inverse, index in sorted(candidates[axis]):
            local = {i: row for i, row in normalized.items() if abs(i-index) <= 32}
            zeros = {a for a, b in local.values() if a == b and _unit(a)}
            for zero in sorted(zeros):
                if zero in (inverse, flag, *point):
                    continue
                try:
                    cert = arithmetic.quotient_certificate(combine(ONE, zero, -1), operand, inverse, local)
                except relation.RelationError:
                    continue
                if cert['kind'] == 'product' and len(cert['rows']) == 3:
                    matches[(inverse, zero)] = cert
            if len(matches) > 8:
                raise relation.RelationError('registered guard reciprocal match8 bound')
        axis_matches.append(matches)
    matches = []
    for (inverse_x, zero_x), xcert in axis_matches[0].items():
        for (inverse_y, zero_y), ycert in axis_matches[1].items():
            if len({inverse_x, inverse_y, zero_x, zero_y, flag, *point}) != 7:
                continue
            for equal, equal_cert in _product_outputs(zero_x, zero_y, normalized):
                for forbidden, forbidden_cert in _product_outputs(flag, equal, normalized):
                    assertions = [i for i, (a, b) in normalized.items()
                                  if not b and a in (forbidden, canonical((c, -v) for c, v in forbidden))]
                    if len(assertions) == 1:
                        matches.append(dict(inverse_x=inverse_x,inverse_y=inverse_y,
                            zero_x=zero_x,zero_y=zero_y,x=xcert,y=ycert,equal=equal,
                            equal_certificate=equal_cert,forbidden=forbidden,
                            forbidden_certificate=forbidden_cert,assertion=assertions[0]))
    if len(matches) != 1:
        raise relation.RelationError('registered guard one complete identity exclusion required')
    certificate = matches[0]
    selected = set(links) | {certificate['assertion']}
    for key in ('x','y','equal_certificate','forbidden_certificate'):
        selected.update(certificate[key]['rows'])
    return dict(identity=first,metadata_sha256=checked['metadata_sha256'],point=point,
        flag=flag,certificate=certificate,selected_rows=[records[i] for i in sorted(selected)],
        scope='Actual registered payload identity exclusion rows. Caller/native fallback '
              'association, kernel, complete relation soundness and legal construction OPEN')


def recheck(checked, extracted):
    obj, point, flag = _boundary(checked)
    raw, normalized = arithmetic.normalize_selection(extracted,obj,checked['metadata_sha256'])
    def lc(value):
        if not isinstance(value,(list,tuple)):
            raise relation.RelationError('registered guard canonical LC required')
        result = []
        for pair in value:
            if not isinstance(pair,(list,tuple)) or len(pair) != 2:
                raise relation.RelationError('registered guard canonical LC pair required')
            c,v = pair
            relation.natural(c,obj['domain_size'])
            relation.natural(v,relation.MODULUS)
            result.append((c,v))
        result = tuple(result)
        if canonical(result) != result:
            raise relation.RelationError('registered guard noncanonical LC')
        return result
    if tuple(lc(v) for v in extracted['point']) != point or lc(extracted['flag']) != flag:
        raise relation.RelationError('registered guard exact leaf and flag LC required')
    c = dict(extracted['certificate'])
    expected = {'inverse_x','inverse_y','zero_x','zero_y','x','y','equal',
                'equal_certificate','forbidden','forbidden_certificate','assertion'}
    if set(c) != expected:
        raise relation.RelationError('registered guard closed certificate required')
    for key in ('inverse_x','inverse_y','zero_x','zero_y','equal','forbidden'):
        c[key] = lc(c[key])
    for key in ('x','y','equal_certificate','forbidden_certificate'):
        c[key] = dict(c[key])
        for field in ('numerator','denominator','quotient','output','auxiliary'):
            if field in c[key]:
                c[key][field] = lc(c[key][field])
    for axis, operand, zero, inverse in (
            ('x',point[0],c['zero_x'],c['inverse_x']),
            ('y',combine(point[1],ONE,-1),c['zero_y'],c['inverse_y'])):
        actual = arithmetic.quotient_certificate(combine(ONE,zero,-1),operand,inverse,normalized)
        if actual != c[axis] or actual['kind'] != 'product' or len(actual['rows']) != 3:
            raise relation.RelationError('registered guard reciprocal certificate changed')
    for left,right,output,key in ((c['zero_x'],c['zero_y'],c['equal'],'equal_certificate'),
                                 (flag,c['equal'],c['forbidden'],'forbidden_certificate')):
        if arithmetic.product_certificate(left,right,output,normalized) != c[key]:
            raise relation.RelationError('registered guard conjunction certificate changed')
    assertion = normalized.get(c['assertion'])
    if assertion not in ((c['forbidden'],()),(canonical((col,-v) for col,v in c['forbidden']),())):
        raise relation.RelationError('registered guard forbidden zero assertion changed')
    return raw,normalized,point,flag,c
