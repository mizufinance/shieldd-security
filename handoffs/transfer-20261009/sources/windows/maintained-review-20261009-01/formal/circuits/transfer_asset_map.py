"""Bounded asset-map source arithmetic and original-row ingress.

Accepted captures must retain two ordinary full ordered-row comparisons and a
repeat. This checker stops at the asset/hash boundary. Hash26, native codecs,
kernel proof and the full Transfer relation remain separate obligations.
"""
import hashlib
import re

from . import transfer_relation as relation, transfer_arithmetic as arithmetic
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical, combine, source_index

P = relation.MODULUS
SCOPE = 'one balance asset-map source boundary; actual rows/hash/native/codec joins open'
VALUE_NAMES = ('u', 'tv', 'den1', 'inv1', 'x1', 'gx1', 'x2', 'gx2', 'square',
               'qr_root', 'x', 'y_squared', 'y', 's', 't', 'plus', 'den', 'zero', 'inv')
K = -40964 % P
C1 = 40962 * pow(K, -1, P) % P
C2 = pow(K, -2, P)
D = -10240 * pow(10241, -1, P) % P
ONE = ((0, 1),)


def _constant(value):
    return canonical([(0, value)])


def _scale(value, factor):
    return canonical((c, v * factor) for c, v in value)


def inspect_metadata(data, accepted_roles):
    """Validate a closed captured cone and independently check its equations.

    An accepted caller supplies the exact asset reference and shared LCs. Source
    operation matching and row extraction do not certify a native Rust program.
    """
    if not isinstance(data, bytes) or len(data) > 4 * 1024 * 1024:
        raise relation.RelationError('asset-map metadata byte bound')
    try:
        obj = relation.record(data)
    except RecursionError as error:
        raise relation.RelationError('asset-map JSON nesting bound') from error
    keys = {'schema', 'family', 'scope', 'relation_digest', 'domain_size', 'full_rows',
            'constant_copy', 'ordinary_full_ordered_rows_equal', 'repeated_observations_equal',
            'asset', 'hash', 'values', 'y_bits', 'cofactor', 'cofactor_aux',
            'constraint_products', 'qr', 'canonical', 'expressions', 'nodes'}
    deferred = obj.get('schema') == 'shieldd-transfer-asset-map-v2'
    if deferred: keys.add('asserted_squares')
    if set(obj) != keys or (obj['schema'], obj['family'], obj['scope']) != (
            'shieldd-transfer-asset-map-v2' if deferred else 'shieldd-transfer-asset-map-v1', 'transfer', SCOPE):
        raise relation.RelationError('asset-map closed schema/scope')
    if not isinstance(accepted_roles, dict) or not isinstance(accepted_roles.get('metadata'), dict):
        raise relation.RelationError('asset-map accepted caller required')
    accepted = accepted_roles['metadata']
    if (any(obj.get(k) != accepted.get(k) for k in
            ('relation_digest', 'domain_size', 'full_rows', 'constant_copy')) or
            not isinstance(obj['relation_digest'], str) or
            not re.fullmatch('[0-9a-f]{64}', obj['relation_digest']) or
            obj['ordinary_full_ordered_rows_equal'] is not True or
            obj['repeated_observations_equal'] is not True):
        raise relation.RelationError('asset-map pending/relation identity')
    domain = relation.natural(obj['domain_size'], 2**32)
    count = relation.natural(obj['full_rows'], domain + 1)
    copy = relation.natural(obj['constant_copy'], domain)
    if domain < 4 or domain & (domain - 1) or not count or copy < 3:
        raise relation.RelationError('asset-map relation shape')
    observed = _expressions(obj['expressions'], domain, copy, 4096, 'asset-map')
    captured = dict(observed)
    if sum(len(lc) for lc in observed.values()) > 65536:
        raise relation.RelationError('asset-map LC term bound')
    required = set()
    asserted = {}
    if deferred:
        entries=obj['asserted_squares']
        if not isinstance(entries,list) or len(entries)!=2:
            raise relation.RelationError('asset-map exact two asserted squares')
        try:
            expected=[(obj['qr'][0],obj['values'][9],obj['qr'][1]),
                      (obj['constraint_products'][0],obj['values'][12],obj['values'][11])]
        except (KeyError,IndexError,TypeError) as error:
            raise relation.RelationError('asset-map asserted square role shape') from error
        for item,wanted in zip(entries,expected):
            if not isinstance(item,dict) or set(item)!={'square','base','target'} or tuple(item[k] for k in ('square','base','target'))!=wanted:
                raise relation.RelationError('asset-map exact asserted square source roles')
            if any(not isinstance(ref,dict) or set(ref)!={'source'} for ref in wanted):
                raise relation.RelationError('asset-map asserted square actual source handles')
            square,base,target=(source_index(ref['source']) for ref in wanted)
            if square[0]!=2 or square in captured or square in asserted or base[0]!=1 or base not in captured or target not in captured:
                raise relation.RelationError('asset-map unmapped asserted square/operand/RHS coverage')
            asserted[square]=(base,target)

    def value(ref):
        if not isinstance(ref, dict) or len(ref) != 1:
            raise relation.RelationError('asset-map observed reference')
        if set(ref) == {'source'}:
            handle = source_index(ref['source'])
            if handle in asserted:
                base,target=asserted[handle]
                required.update((handle,base,target))
                # This is an asserted-square row plan, not a compiler LC.
                # Only the mandatory original base^2=target row can justify it.
                return captured[target]
            if handle not in observed:
                raise relation.RelationError('asset-map missing role expression')
            required.add(handle)
            return observed[handle]
        if set(ref) == {'native'}:
            encoded = ref['native']
            if not isinstance(encoded, str) or not re.fullmatch('[0-9a-f]{64}', encoded) or int(encoded, 16) >= P:
                raise relation.RelationError('asset-map noncanonical native reference')
            return _constant(int(encoded, 16))
        raise relation.RelationError('asset-map unknown observed reference')

    def array(refs, size):
        if not isinstance(refs, list) or len(refs) != size:
            raise relation.RelationError('asset-map role array shape')
        return tuple(value(ref) for ref in refs)

    def witness(ref):
        if not isinstance(ref, dict) or set(ref) != {'source'} or source_index(ref['source'])[0] != 1:
            raise relation.RelationError('asset-map witness role required')
        return source_index(ref['source'])

    if any(not isinstance(obj[k], dict) or set(obj[k]) != {'source'} for k in ('asset', 'hash')):
        raise relation.RelationError('asset-map actual ingress sources required')
    asset, hash_lc = value(obj['asset']), value(obj['hash'])
    if obj['asset'] != accepted.get('caller', {}).get('asset'):
        raise relation.RelationError('asset-map caller asset source mismatch')
    values = dict(zip(VALUE_NAMES, array(obj['values'], 19)))
    if obj['values'][0] != obj['hash']:
        raise relation.RelationError('asset-map hash/u source mismatch')
    bits = obj['y_bits']
    if not isinstance(bits, list) or len(bits) != 255:
        raise relation.RelationError('asset-map canonical255 bit count')
    handles = tuple(source_index(bit) for bit in bits)
    if len(set(handles)) != 255 or any(h[0] != 1 or h not in observed for h in handles):
        raise relation.RelationError('asset-map canonical bit witness alias/coverage')
    required.update(handles)
    points, aux = obj['cofactor'], obj['cofactor_aux']
    if not isinstance(points, list) or len(points) != 4 or not isinstance(aux, list) or len(aux) != 3:
        raise relation.RelationError('asset-map three cofactor doublings inventory')
    points = tuple(array(point, 2) for point in points)
    aux = tuple(array(a, 7) for a in aux)
    products = array(obj['constraint_products'], 4)
    qr = array(obj['qr'], 2)
    encoding = array(obj['canonical'], 2)
    own_witnesses = {witness(obj['values'][i]) for i in (3, 8, 9, 12, 17, 18)}
    own_witnesses.update(witness(a[6]) for a in obj['cofactor_aux'])
    if len(own_witnesses) != 9 or own_witnesses & set(handles):
        raise relation.RelationError('asset-map owned witness alias')
    roots = {source_index(ref['source']) for ref in (obj['asset'], obj['hash'])
             if set(ref) == {'source'}}
    if len(roots) != 2:
        raise relation.RelationError('asset-map asset/hash ingress alias')
    if set(handles) & roots or own_witnesses & roots:
        raise relation.RelationError('asset-map owned witness/ingress alias')
    nodes = obj['nodes']
    if not isinstance(nodes, list) or len(nodes) > 16384:
        raise relation.RelationError('asset-map DAG bound')
    node_map = {}
    previous = -1
    for node in nodes:
        if (not isinstance(node, dict) or set(node) != {'index', 'multiply', 'left', 'right'} or
                type(node['multiply']) is not bool):
            raise relation.RelationError('asset-map DAG node closed shape')
        index = relation.natural(node['index'], 2**32)
        if index <= previous or (2, index) in roots:
            raise relation.RelationError('asset-map DAG ordering/source/ingress mismatch')
        previous = index
        children = tuple(source_index(node[k]) for k in ('left', 'right'))
        if any(h[0] != 2 and h not in observed or h[0] == 2 and h[1] >= index for h in children):
            raise relation.RelationError('asset-map missing/non-topological DAG child')
        node_map[index] = (node['multiply'], children)
    mandatory = set(required)
    mandatory.difference_update(asserted)
    derived_terms = 0
    # Compiler affine/folded operations add no physical product witness.
    # Reconstruct their LCs from the complete source DAG, checking every LC
    # that was also captured. Every genuine product keeps its compiler LC.
    for index, (multiply, children) in node_map.items():
        if any(h not in observed for h in children):
            raise relation.RelationError('asset-map missing source predecessor/root')
        a,b=(observed[h] for h in children)
        folded=next(((s,o) for s,o in ((a,b),(b,a)) if not s or len(s)==1 and s[0][0]==0),None)
        expected=combine(a,b) if not multiply else (_scale(folded[1],folded[0][0][1] if folded[0] else 0) if folded is not None else None)
        if expected is None:
            if (2,index) in asserted:
                base,target=asserted[2,index]
                if not multiply or children!=(base,base):
                    raise relation.RelationError('asset-map asserted square exact source AST')
                observed[2,index]=captured[target]
                mandatory.update((base,target))
            elif (2,index) not in captured:
                raise relation.RelationError('asset-map missing actual nonlinear compiler LC')
            else:mandatory.update(((2,index),*children))
        else:
            if (2,index) in captured and captured[2,index]!=expected:
                raise relation.RelationError('asset-map derived affine/folded LC mismatch')
            observed[2,index]=expected
        derived_terms+=len(observed[2,index])
        if derived_terms>262144:
            raise relation.RelationError('asset-map symbolic LC term bound')
    # Every retained node is reached from an observed role, stopping at exactly
    # the two ingress roots. Arbitrary additional witness leaves are rejected.
    pending = list(required)
    reached = set()
    allowed = set(handles) | own_witnesses | roots
    while pending:
        handle = pending.pop()
        if handle in roots or handle[0] == 0:
            required.add(handle)
            continue
        if handle[0] == 1:
            if handle not in allowed:
                raise relation.RelationError('asset-map unknown witness boundary')
            required.add(handle)
            continue
        if handle[1] not in node_map:
            raise relation.RelationError('asset-map incomplete source cone')
        if handle[1] in reached:
            continue
        reached.add(handle[1])
        pending.extend(node_map[handle[1]][1])
    complete = required | {(2,i) for i in reached}
    if any(h in asserted for _,children in node_map.values() for h in children) or not set(asserted)<={(2,i) for i in reached}:
        raise relation.RelationError('asset-map asserted square cannot be a compiler expression predecessor')
    if reached != set(node_map) or not mandatory <= set(captured) or not set(captured) <= complete:
        raise relation.RelationError('asset-map exact source cone coverage')
    shared = accepted_roles.get('observed')
    if not isinstance(shared, dict) or source_index(obj['asset']['source']) not in shared:
        raise relation.RelationError('asset-map missing accepted caller asset LC')
    for handle, lc in observed.items():
        if handle in shared and lc != shared[handle]:
            raise relation.RelationError('asset-map changed caller/shared source LC')
    nonlinear, lookup = [], {}
    for index, (multiply, children) in node_map.items():
        a, b = (observed[h] for h in children)
        output = observed[2, index]
        if not multiply:
            if output != combine(a, b):
                raise relation.RelationError('asset-map add-node LC mismatch')
            continue
        folded = next(((s, o) for s, o in ((a, b), (b, a))
                       if not s or len(s) == 1 and s[0][0] == 0), None)
        if folded is not None:
            scalar, other = folded
            if output != _scale(other, scalar[0][1] if scalar else 0):
                raise relation.RelationError('asset-map folded multiply LC mismatch')
        else:
            nonlinear.append((index, a, b, output))
        # Repeated operations may allocate distinct materialized products.
        # Keep their different LCs rather than silently treating them as equal.
        for key in ((a, b), (b, a)):
            lookup.setdefault(key, set()).add(output)

    def multiply(a, b, expected=None):
        scalar = next(((s, o) for s, o in ((a, b), (b, a))
                       if not s or len(s) == 1 and s[0][0] == 0), None)
        if scalar is not None:
            s, other = scalar
            result = _scale(other, s[0][1] if s else 0)
        else:
            candidates = lookup.get((a, b), set())
            if expected is not None and expected in candidates:
                result = expected
            elif len(candidates) == 1:
                result = next(iter(candidates))
            else:
                raise relation.RelationError('asset-map expected source product missing/ambiguous')
        if expected is not None and result != expected:
            raise relation.RelationError('asset-map expected product role mismatch')
        return result

    def equal(actual, expected, label):
        if actual != expected:
            raise relation.RelationError('asset-map independent equation mismatch: ' + label)

    v = values
    multiply(_scale(v['u'], 5), v['u'], v['tv'])
    equal(v['den1'], combine(ONE, v['tv']), 'first denominator')
    equal(v['x1'], _scale(v['inv1'], -C1), 'first x')
    cubic = multiply(combine(v['x1'], _constant(C1)), v['x1'])
    multiply(combine(cubic, _constant(C2)), v['x1'], v['gx1'])
    equal(v['x2'], combine(_scale(v['x1'], -1), _constant(-C1)), 'alternative x')
    multiply(v['tv'], v['gx1'], v['gx2'])
    select = lambda yes, no, result=None: combine(no, multiply(v['square'], combine(yes, no, -1),
                  combine(result, no, -1) if result is not None else None))
    equal(v['x'], select(v['x1'], v['x2'], v['x']), 'selected x')
    equal(v['y_squared'], select(v['gx1'], v['gx2'], v['y_squared']), 'selected y square')
    multiply(v['qr_root'], v['qr_root'], qr[0])
    equal(qr[1], select(v['gx1'], _scale(v['gx1'], 5), qr[1]), 'QR selector')
    multiply(v['y'], v['y'], products[0])
    equal(v['s'], _scale(v['x'], K), 's scaling')
    equal(v['t'], _scale(v['y'], K), 't scaling')
    equal(v['plus'], combine(v['s'], ONE), 'plus')
    multiply(v['plus'], v['t'], v['den'])
    multiply(v['den'], v['inv'], products[1])
    multiply(v['den'], v['zero'], products[2])
    multiply(v['inv'], v['zero'], products[3])
    px = multiply(multiply(v['inv'], v['plus']), v['s'], points[0][0])
    py = multiply(multiply(v['inv'], v['t']), combine(v['s'], ONE, -1),
                  combine(points[0][1], v['zero'], -1))
    equal(points[0], (px, combine(py, v['zero'])), 'rational image')
    for i, ((x, y), a, result) in enumerate(zip(points, aux, points[1:])):
        xx, yy, dt, plus, minus, divisor, inverse = a
        multiply(x, x, xx)
        multiply(y, y, yy)
        multiply(xx, yy, _scale(dt, pow(D, -1, P)))
        equal(plus, combine(ONE, dt), 'double plus')
        equal(minus, combine(ONE, dt, -1), 'double minus')
        multiply(plus, minus, divisor)
        cross = lookup.get((x, y), set())
        if len(cross) > 8:
            raise relation.RelationError('asset-map repeated cross product bound')
        matched = False
        for xy in cross:
            for yx in cross:
                for times_minus in lookup.get((combine(xy, yx), minus), set()):
                    if result[0] in lookup.get((times_minus, inverse), set()):
                        matched = True
        if not matched:
            raise relation.RelationError('asset-map double x source equation mismatch')
        multiply(multiply(combine(yy, xx), plus), inverse, result[1])
    bit_lcs = tuple(observed[h] for h in handles)
    equal(encoding[0], canonical((c, n * 2**i) for i, bit in enumerate(bit_lcs)
                                for c, n in bit), 'canonical reconstruction')
    le = ONE
    comparisons = []
    for i, bit in enumerate(bit_lcs):
        flag = (P - 1) >> i & 1
        factor = bit if flag else combine(ONE, bit, -1)
        product = multiply(le, factor)
        after = combine(combine(ONE, bit, -1), product) if flag else product
        comparisons.append((le, bit, factor, product, after, flag))
        le = after
    equal(encoding[1], le, 'canonical strict modulus endpoint')
    return dict(metadata=obj, observed=observed, captured_observed=captured, asserted_square_nodes=asserted,
                values=values, points=points, auxiliary=aux,
                bits=bit_lcs, nonlinear=nonlinear, comparisons=comparisons, products=products,
                qr=qr, canonical=encoding, asset=asset, hash=hash_lc,
                metadata_sha256=hashlib.sha256(data).hexdigest())


def obligations(checked):
    """Original squared-row templates; quotient materializations stay explicit."""
    obj = checked['metadata']
    copy = obj['constant_copy']
    outline = lambda lc: canonical((copy if c == 0 else c, n) for c, n in lc)
    required = {(canonical([(0, 1), (copy, -1)]), ()): ['constant-copy']}
    products, squares = [], []

    def require(label, a, b=()):
        if a or b:
            required.setdefault((outline(a), outline(b)), []).append(label)

    for i, bit in enumerate(checked['bits']):
        require('canonical.boolean' + str(i), bit, bit)
    v = checked['values']
    for name in ('square', 'zero'):
        require(name + '.boolean', v[name], v[name])
    for label, left, right in (
            ('QR', *checked['qr']), ('selected-square', checked['products'][0], v['y_squared']),
            ('total-inverse', checked['products'][1], combine(ONE, v['zero'], -1)),
            ('denominator-zero', checked['products'][2], ()), ('inverse-zero', checked['products'][3], ()),
            ('canonical-reconstruction', checked['canonical'][0], v['y']),
            ('canonical-endpoint', checked['canonical'][1], ONE),
            ('parity', checked['bits'][0], v['square'])):
        require(label, combine(left, right, -1))
    for index, a, b, output in checked['nonlinear']:
        if a == b:
            # The compiler may fuse an asserted square into its RHS expression.
            require('node' + str(index), a, output)
        else:
            products.append(('node' + str(index), outline(combine(a, b, -1)),
                             outline(combine(a, b)), outline(output), None))
    inverses = [(v['den1'], v['inv1'])] + [(a[5], a[6]) for a in checked['auxiliary']]
    for i, (denominator, inverse) in enumerate(inverses):
        products.append(('division' + str(i), outline(combine(inverse, denominator, -1)),
                         outline(combine(inverse, denominator)), None, outline(ONE)))
    return required, products, squares


def extract(data, stream, accepted_roles):
    checked = inspect_metadata(data, accepted_roles)
    obj = checked['metadata']
    required, products, squares = obligations(checked)
    result = arithmetic.extract_templates(stream, obj['relation_digest'], obj['domain_size'],
                                         obj['full_rows'], required, products, squares, label='asset-map')
    result.update(metadata_sha256=checked['metadata_sha256'],
                  scope='actual bounded asset-map DAG/constraints only; hash26/native/kernel/full Transfer open')
    return result


def certificates(data, extracted, accepted_roles):
    """Recheck persisted rows; a receipt hash alone cannot supply an equation."""
    checked = inspect_metadata(data, accepted_roles)
    raw, rows = arithmetic.normalize_selection(extracted, checked['metadata'], checked['metadata_sha256'])
    nonlinear = [dict(node=i, **arithmetic.product_certificate(a, b, out, rows))
                 for i, a, b, out in checked['nonlinear']]
    v = checked['values']
    inverses = [(v['den1'], v['inv1'])] + [(a[5], a[6]) for a in checked['auxiliary']]
    quotients = [arithmetic.quotient_certificate(ONE, den, inv, rows) for den, inv in inverses]
    required, _, _ = obligations(checked)
    copy = checked['metadata']['constant_copy']
    normalize = lambda lc: canonical((0 if c == copy else c, n) for c, n in lc)
    used = {i for c in nonlinear + quotients for i in c['rows']}
    for a, b in required:
        equation = (normalize(a), normalize(b))
        alternative = (_scale(equation[0], -1), equation[1])
        matches = [i for i, row in rows.items() if row in (equation, alternative)]
        if not matches:
            raise relation.RelationError('asset-map retained assertion/Boolean/square missing')
        used.update(matches)
    if used != set(raw):
        raise relation.RelationError('asset-map retained exact physical row coverage')
    return dict(checked=checked, raw=raw, rows=rows, nonlinear=nonlinear, quotients=quotients)


def generate_row_modules(data, extracted, accepted_roles, *, chunk_size=16):
    """Small source-generated row implications with explicit assignment premises.

    These modules establish captured products, Boolean/square rows, inverse
    materializations and assertions. They do not assert map/native equivalence,
    a full relation conclusion or legal-input construction.
    """
    from .generate_hash_round import linear, signed, _signature_audits
    from .transfer_ownership import generate_quotient_boundaries
    if type(chunk_size) is not int or not 1 <= chunk_size <= 32:
        raise relation.RelationError('asset-map row module chunk bound')
    result = certificates(data, extracted, accepted_roles)
    checked, raw, rows = result['checked'], result['raw'], result['rows']
    obj = checked['metadata']
    copy = obj['constant_copy']
    link = next(i for i, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ()))
    modules = {}

    def base(name, indices, imports='import ShielddSecurity.Compiler\n'):
        selected = sorted(set(indices) | {link})
        return f'''{imports}set_option maxHeartbeats 500000
namespace ShielddSecurity.{name}
-- Bounded original-row implication; native/hash26/full Transfer joins remain open.
-- Metadata SHA256 {checked['metadata_sha256']}; relation {obj['relation_digest']}.
def modulus : Nat := {P}
def originalRows : List Nat := {selected}
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in selected)+f''']
def rows : List Row := Compiler.unoutlineRows {copy} rawRows
theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
'''

    def finish(source, name, exports):
        source += ''.join('#print axioms '+export+'\n' for export in ['constantLink', *exports])
        return _signature_audits(source + 'end ShielddSecurity.' + name + '\n')

    for start in range(0, len(checked['nonlinear']), chunk_size):
        name = 'RuntimeTransferAssetMapProducts' + str(start // chunk_size)
        nodes = checked['nonlinear'][start:start+chunk_size]
        certs = result['nonlinear'][start:start+chunk_size]
        source = base(name, [i for cert in certs for i in cert['rows']],
                      'import ShielddSecurity.ScalarRows\nimport ShielddSecurity.Compiler\n')
        exports = []
        for (index, a, b, output), cert in zip(nodes, certs):
            prefix = 'node' + str(index)
            left, right = (b, a) if cert.get('swapped') else (a, b)
            if cert['kind'] == 'square':
                datum = '.square'
            elif cert['kind'] == 'product':
                datum = '.product ' + linear(cert['auxiliary'])
            else:
                datum = ('.foldedLeft ' if cert['kind'] == 'folded_left' else '.foldedRight ') + f'({signed(cert["coefficient"])} : Int)'
            source += f'''theorem {prefix}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho {linear(output)} = eval rho {linear(a)} * eval rho {linear(b)} := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have checked := ScalarRows.checked_product_sound rho one four rows normalized
    {linear(left)} {linear(right)} {linear(output)} ({datum}) (by decide)
  simpa only [mul_comm] using checked
'''
            exports.append(prefix + '_sound')
        modules[name] = finish(source, name, exports)

    required, _, _ = obligations(checked)
    normalized = lambda lc: canonical((0 if c == copy else c, n) for c, n in lc)
    direct = []
    for (a, b), labels in required.items():
        a, b = normalized(a), normalized(b)
        index = next(i for i, row in rows.items() if row in ((a, b), (_scale(a, -1), b)))
        if index == link:
            continue
        direct.append((index, a, b, labels))
    for start in range(0, len(direct), chunk_size):
        name = 'RuntimeTransferAssetMapConstraints' + str(start // chunk_size)
        entries = direct[start:start+chunk_size]
        source = base(name, [i for i, _, _, _ in entries])
        if any(len(a) + len(b) > 128 for _, a, b, _ in entries):
            # Canonical255 reconstruction retains its exact 256-term LC.
            # Finite depth covers elaboration/normalization of this literal
            # row; bounded products and smaller constraint modules are stable.
            source = source.replace('set_option maxHeartbeats 500000\n',
                                    'set_option maxHeartbeats 500000\nset_option maxRecDepth 4096\n', 1)
        exports = []
        for offset, (index, a, b, _) in enumerate(entries):
            prefix = 'constraint' + str(start + offset)
            if b:
                conclusion = f'eval rho {linear(b)} = eval rho {linear(a)} * eval rho {linear(a)}'
                proof = f'exact Compiler.checked_square_sound rho rows {linear(a)} {linear(b)} normalized (by decide)'
            else:
                left = a if rows[index][0] == a else _scale(a, -1)
                conclusion = f'eval rho {linear(a)} = 0'
                proof = f'''have checked := Compiler.checked_assertion_sound rho rows {linear(left)} [] normalized (by decide)
  have zero : eval rho [] = (0 : F) := by rfl
  rw [zero] at checked
'''
                if left == a:
                    proof += '  exact checked'
                else:
                    proof += f'''  have equal := Compiler.canonical_equal rho {linear(left)} (scaleLinear (-1) {linear(a)}) (by decide)
  rw [eval_scale] at equal
  have negated : -(eval rho {linear(a)}) = 0 := by simpa using equal.symm.trans checked
  exact neg_eq_zero.mp negated'''
            source += f'''theorem {prefix}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) : {conclusion} := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  {proof}
'''
            exports.append(prefix + '_sound')
        modules[name] = finish(source, name, exports)
    name = 'RuntimeTransferAssetMapInverses'
    inverse_indices = {link} | {i for cert in result['quotients'] for i in cert['rows']}
    modules[name] = generate_quotient_boundaries(
        dict(outline=copy, rows={i: raw[i] for i in sorted(inverse_indices)}, certificates=result['quotients']),
        checked['metadata_sha256'], obj['relation_digest'], namespace=name)
    return modules


def generate_comparison_modules(data, extracted, accepted_roles, *, chunk_size=8):
    """Indexed bounded chunks of the actual canonical255 comparison.

    Each chunk preserves its real input state and bit order. Composition with
    FieldEncoding still needs the whole original reconstruction/endpoint rows;
    an isolated fragment cannot claim the field bound.
    """
    from .generate_hash_round import linear, signed, _signature_audits
    if type(chunk_size) is not int or not 1 <= chunk_size <= 16:
        raise relation.RelationError('asset-map comparator chunk bound')
    result = certificates(data, extracted, accepted_roles)
    checked, raw, rows = result['checked'], result['raw'], result['rows']
    copy = checked['metadata']['constant_copy']
    link = next(i for i, row in raw.items() if row == (canonical([(0, 1), (copy, -1)]), ()))
    comparisons = checked['comparisons']
    if len(comparisons) != 255:
        raise relation.RelationError('asset-map comparator full width')
    modules = {}
    for start in range(0, 255, chunk_size):
        fragment = comparisons[start:start+chunk_size]
        certs = [arithmetic.product_certificate(before, factor, product, rows)
                 for before, _, factor, product, _, _ in fragment]
        if any(cert.get('swapped') for cert in certs):
            raise relation.RelationError('asset-map indexed comparator orientation unsupported')
        indices = {link} | {i for c in certs for i in c['rows']}
        for _, bit, _, _, _, _ in fragment:
            indices.add(next(i for i, row in rows.items() if row == (bit, bit)))
        indices = sorted(indices)
        positions = {original: dense for dense, original in enumerate(indices)}
        name = 'RuntimeTransferAssetMapComparison' + str(start // chunk_size)
        source = f'''import ShielddSecurity.ScalarIndexed
import ShielddSecurity.ScalarComparisonBounds
set_option maxHeartbeats 500000
namespace ShielddSecurity.{name}
-- Only actual comparison bits {start}..{start+len(fragment)-1}; no full canonical bound.
-- Metadata SHA256 {checked['metadata_sha256']}.
def modulus : Nat := {P}
def originalRows : List Nat := {indices}
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in indices)+f''']
def rows : List Row := Compiler.unoutlineRows {copy} rawRows
def initial : Linear := {linear(fragment[0][0])}
def endpoint : Linear := {linear(fragment[-1][4])}
theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by
  exact ScalarIndexed.checked_row_membership modulus rawRows {positions[link]} _ (by decide)
def indexedSteps : List ScalarIndexed.StepData := [
'''
        records = []
        for (before, bit, factor, product, after, flag), cert in zip(fragment, certs):
            kind = cert['kind']
            if kind == 'product':
                minus, plus = (positions[i] for i in cert['rows'])
                datum = f'.product {minus} {plus} ' + linear(cert['auxiliary'])
            elif kind == 'square':
                datum = '.square ' + str(positions[cert['rows'][0]])
            else:
                datum = ('.foldedLeft ' if kind == 'folded_left' else '.foldedRight ') + f'({signed(cert["coefficient"])} : Int)'
            records.append('{ before := '+linear(before)+', left := '+linear(bit)+
                           ', after := '+linear(after)+', right := '+('true' if flag else 'false')+
                           ', factor := '+linear(factor)+', target := '+linear(product)+', product := '+datum+' }')
        source += ',\n'.join(records) + f''']
def steps : List ScalarRows.StepData := indexedSteps.map ScalarIndexed.StepData.ordinary
theorem endpoint_checked : ScalarComparisonBounds.endpoint initial steps = endpoint := by rfl
theorem bits_certificate : ScalarBits.checkBits modulus rows (steps.map ScalarRows.StepData.left) = true := by decide
theorem chain_certificate : ScalarRows.checkChain modulus rows initial steps = true := by
  exact ScalarIndexed.checked_chain_membership modulus rows initial indexedSteps (by decide)
theorem actual_fragment {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho endpoint = ScalarRows.polynomialChain rho (eval rho initial) steps := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have recurrence := ScalarRows.checked_chain_sound rho one four rows normalized initial steps chain_certificate
  rw [ScalarComparisonBounds.endpoint_value, endpoint_checked] at recurrence
  exact recurrence
'''
        source += ''.join('#print axioms '+n+'\n' for n in
                          ('constantLink', 'endpoint_checked', 'bits_certificate', 'chain_certificate', 'actual_fragment'))
        modules[name] = _signature_audits(source + 'end ShielddSecurity.' + name + '\n')
    return modules


def generate_encoding_module(data, extracted, accepted_roles, *, chunk_size=8):
    """Compose every255 real comparison step and its original encoding rows.

    Local certificates are transported into the union by symbolic membership;
    the full chain is assembled with an append lemma rather than rechecking a
    wide constraint walk. Canonicality and parity are conclusions of those rows.
    """
    from .generate_hash_round import linear, _signature_audits
    local = generate_comparison_modules(data, extracted, accepted_roles, chunk_size=chunk_size)
    result = certificates(data, extracted, accepted_roles)
    checked, raw, rows = result['checked'], result['raw'], result['rows']
    copy = checked['metadata']['constant_copy']
    indices = {next(i for i, r in raw.items() if r == (canonical([(0, 1), (copy, -1)]), ()))}
    for left, right in ((checked['canonical'][0], checked['values']['y']),
                        (checked['canonical'][1], ONE),
                        (checked['bits'][0], checked['values']['square'])):
        equation = combine(left, right, -1)
        indices.add(next(i for i, r in rows.items() if r in ((equation, ()), (_scale(equation, -1), ()))))
    names = list(local)
    count = len(names)
    alias = lambda i: 'ShielddSecurity.' + names[i]
    name = 'RuntimeTransferAssetMapEncoding'
    source = ''.join('import ShielddSecurity.'+n+'\n' for n in names)
    source += f'''import ShielddSecurity.FieldEncoding
import ShielddSecurity.ScalarChainComposition
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
-- Complete original canonical255 chain, reconstruction, endpoint and parity.
-- Metadata SHA256 {checked['metadata_sha256']}; upstream native codec laws separate.
def modulus : Nat := {P}
def originalBoundaryRows : List Nat := {sorted(indices)}
def boundaryRawRows : List Row := [
'''+',\n'.join('⟨'+linear(raw[i][0])+','+linear(raw[i][1])+'⟩' for i in sorted(indices))+f''']
def boundaryRows : List Row := Compiler.unoutlineRows {copy} boundaryRawRows
def rawRows : List Row := '''+' ++ '.join(alias(i)+'.rawRows' for i in range(count))+' ++ boundaryRawRows\n'
    source += 'def rows : List Row := '+' ++ '.join(alias(i)+'.rows' for i in range(count))+' ++ boundaryRows\n'
    source += f'''theorem constantLink : Compiler.checkRow modulus boundaryRawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
theorem rows_normalized : rows = Compiler.unoutlineRows {copy} rawRows := by
  simp only [rows, rawRows, boundaryRows, Compiler.unoutlineRows, List.map_append]
  rfl
'''
    exports = ['constantLink', 'rows_normalized']
    # Membership remains symbolic in the chunk rows; no Cartesian row walk.
    for i in range(count):
        source += f'''theorem included{i} : ∀ item ∈ {alias(i)}.rows, item ∈ rows := by
  intro item member
  simp only [rows, List.mem_append]
  tauto
def suffix{i} : List ScalarRows.StepData := '''
        source += alias(i)+'.steps'+(f' ++ suffix{i+1}' if i+1 < count else '')+'\n'
        exports.append('included'+str(i))
    # Forward references are not legal definitions: place suffixes last-first.
    pieces = source.splitlines(keepends=True)
    suffixes = [line for line in pieces if line.startswith('def suffix')]
    source = ''.join(line for line in pieces if not line.startswith('def suffix')) + ''.join(reversed(suffixes))
    source += 'def steps : List ScalarRows.StepData := suffix0\n'
    for i in reversed(range(count)):
        a = alias(i)
        source += f'''theorem chain{i} : ScalarRows.checkChain modulus rows {a}.initial suffix{i} = true := by
  have chunkChecked := ScalarChainComposition.chain_monotone modulus {a}.rows rows included{i}
    {a}.initial {a}.steps {a}.chain_certificate
'''
        if i+1 < count:
            source += f'''  exact ScalarChainComposition.chain_append modulus rows {a}.initial {a}.steps suffix{i+1}
    chunkChecked (by rw [{a}.endpoint_checked]; exact chain{i+1})
'''
        else:
            source += '  exact chunkChecked\n'
        source += f'''theorem bits{i} : ScalarBits.checkBits modulus rows (suffix{i}.map ScalarRows.StepData.left) = true := by
  have chunkChecked := ScalarChainComposition.bits_monotone modulus {a}.rows rows included{i}
    ({a}.steps.map ScalarRows.StepData.left) {a}.bits_certificate
'''
        if i+1 < count:
            source += f'''  simpa only [suffix{i}, List.map_append] using
    ScalarChainComposition.bits_append modulus rows ({a}.steps.map ScalarRows.StepData.left)
      (suffix{i+1}.map ScalarRows.StepData.left) chunkChecked bits{i+1}
'''
        else:
            source += '  exact chunkChecked\n'
        source += f'''theorem endpoint{i} : ScalarComparisonBounds.endpoint {a}.initial suffix{i} = {alias(count-1)}.endpoint := by
'''
        if i+1 < count:
            source += f'''  rw [suffix{i}, ScalarChainComposition.endpoint_append, {a}.endpoint_checked]
  exact endpoint{i+1}
'''
        else:
            source += f'  exact {a}.endpoint_checked\n'
        exports.extend(('chain'+str(i), 'bits'+str(i), 'endpoint'+str(i)))
    # Only the three long encoding/assertion rows are checked in this boundary.
    source += f'''theorem boundary_included : ∀ item ∈ boundaryRows, item ∈ rows := by
  intro item member
  simp only [rows, List.mem_append]
  tauto
def value : Linear := {linear(checked['values']['y'])}
def choice : Linear := {linear(checked['values']['square'])}
theorem ending_checked : ScalarComparisonBounds.checkEquality modulus rows {alias(count-1)}.endpoint [(0,1)] = true := by
  have checked : ScalarComparisonBounds.checkEquality modulus boundaryRows {alias(count-1)}.endpoint [(0,1)] = true := by decide
  simp only [ScalarComparisonBounds.checkEquality, Bool.or_eq_true] at checked ⊢
  rcases checked with forward | backward
  · exact Or.inl (ScalarChainComposition.row_monotone modulus boundaryRows rows boundary_included _ forward)
  · exact Or.inr (ScalarChainComposition.row_monotone modulus boundaryRows rows boundary_included _ backward)
theorem rebuild_checked : ScalarComparisonBounds.checkEquality modulus rows
    (ScalarBits.bitLinear (steps.map ScalarRows.StepData.left)) value = true := by
  have checked : ScalarComparisonBounds.checkEquality modulus boundaryRows
      (ScalarBits.bitLinear (steps.map ScalarRows.StepData.left)) value = true := by decide
  simp only [ScalarComparisonBounds.checkEquality, Bool.or_eq_true] at checked ⊢
  rcases checked with forward | backward
  · exact Or.inl (ScalarChainComposition.row_monotone modulus boundaryRows rows boundary_included _ forward)
  · exact Or.inr (ScalarChainComposition.row_monotone modulus boundaryRows rows boundary_included _ backward)
theorem parity_checked : ScalarComparisonBounds.checkEquality modulus rows
    {linear(checked['bits'][0])} choice = true := by
  have checked : ScalarComparisonBounds.checkEquality modulus boundaryRows {linear(checked['bits'][0])} choice = true := by decide
  simp only [ScalarComparisonBounds.checkEquality, Bool.or_eq_true] at checked ⊢
  rcases checked with forward | backward
  · exact Or.inl (ScalarChainComposition.row_monotone modulus boundaryRows rows boundary_included _ forward)
  · exact Or.inr (ScalarChainComposition.row_monotone modulus boundaryRows rows boundary_included _ backward)
theorem maximum_checked : binary (steps.map ScalarRows.StepData.right) = Scalar.modulus - 1 := by decide
theorem actual_encoding {{F : Type}} [Field F] [CharP F modulus]
    (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    codec.decode (eval rho value) = binary (ScalarBits.decodeBits rho (steps.map ScalarRows.StepData.left)) := by
  have normalized : Satisfies rho rows := by
    rw [rows_normalized]
    exact Compiler.unoutline_rows_sound rho {copy} rawRows satisfied
      (ScalarChainComposition.row_monotone modulus boundaryRawRows rawRows
        (by intro item member; simp only [rawRows, List.mem_append]; tauto) _ constantLink)
  exact FieldEncoding.checked_encoding codec rho one four rows normalized steps value
    bits0 chain0 (by
      change ScalarComparisonBounds.checkEquality modulus rows
        (ScalarComparisonBounds.endpoint {alias(0)}.initial suffix0) [(0,1)] = true
      rw [endpoint0]
      exact ending_checked) maximum_checked rebuild_checked
theorem actual_parity {{F : Type}} [Field F] [CharP F modulus]
    (codec : TransferReduction.CanonicalField F) (rho : Nat → F)
    (one : rho 0 = 1) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    codec.decode (eval rho value) % 2 = if ScalarBits.decodeBit rho choice then 1 else 0 := by
  classical
  rw [actual_encoding codec rho one four satisfied, FieldEncoding.binary_parity]
  change (if ScalarBits.decodeBit rho {linear(checked['bits'][0])} then 1 else 0) =
    (if ScalarBits.decodeBit rho choice then 1 else 0)
  have normalized : Satisfies rho rows := by
    rw [rows_normalized]
    exact Compiler.unoutline_rows_sound rho {copy} rawRows satisfied
      (ScalarChainComposition.row_monotone modulus boundaryRawRows rawRows
        (by intro item member; simp only [rawRows, List.mem_append]; tauto) _ constantLink)
  have same := ScalarComparisonBounds.checked_equality rho rows normalized
    {linear(checked['bits'][0])} choice parity_checked
  simp only [ScalarBits.decodeBit, same]
  rfl
'''
    exports += ['boundary_included', 'ending_checked', 'rebuild_checked', 'parity_checked', 'maximum_checked', 'actual_encoding', 'actual_parity']
    source += ''.join('#print axioms '+n+'\n' for n in exports)
    return _signature_audits(source+'end ShielddSecurity.'+name+'\n')
