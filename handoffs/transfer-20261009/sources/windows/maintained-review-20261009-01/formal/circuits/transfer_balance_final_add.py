"""Bounded original-row inference for signed value plus VALUE_BLINDING.

The actual two loop endpoints and final caller commitment are supplied as
canonical LCs, with all three qualified parent identities retained. No source
handle, native endpoint, inverse truth or qualification flag is invented.
Unsupported lowering order or ambiguous physical pairs refuse explicitly.
"""
from . import transfer_relation as relation, transfer_arithmetic as arithmetic
from .transfer_balance_rows import canonical, combine
from .transfer_balance_blinding_fixed import DIGEST

D = -10240 * pow(10241, -1, relation.MODULUS) % relation.MODULUS
ONE = ((0, 1),)


def boundary(roles):
    """Pure LC boundary; actual parent/source association remains the caller's job."""
    import re
    keys = {'relation_digest', 'variable_parent', 'blinding_parent', 'caller_parent',
            'negative', 'unsigned', 'blinded', 'output'}
    if not isinstance(roles, dict) or set(roles) != keys or roles['relation_digest'] != DIGEST:
        raise relation.RelationError('final balance exact role boundary required')
    for key in ('variable_parent', 'blinding_parent', 'caller_parent'):
        if not isinstance(roles[key], str) or not re.fullmatch('[0-9a-f]{64}', roles[key]):
            raise relation.RelationError('final balance qualified parent identity required')
    def lc(value):
        if not isinstance(value, (list, tuple)) or not 1 <= len(value) <= 64:
            raise relation.RelationError('final balance LC bound')
        for term in value:
            if not isinstance(term, (list, tuple)) or len(term) != 2:
                raise relation.RelationError('final balance LC term')
            relation.natural(term[0], 262144)
            if type(term[1]) is not int or not 0 < term[1] < relation.MODULUS:
                raise relation.RelationError('final balance LC coefficient')
        result = tuple(map(tuple, value))
        if canonical(result) != result or any(c == 200692 for c, _ in result):
            raise relation.RelationError('final balance normalized canonical LC required')
        return result
    def point(value):
        if not isinstance(value, (list, tuple)) or len(value) != 2:
            raise relation.RelationError('final balance two coordinates required')
        return tuple(lc(side) for side in value)
    return dict(roles, negative=lc(roles['negative']),
                **{key: point(roles[key]) for key in ('unsigned', 'blinded', 'output')})


class Matcher:
    """Finite adaptive matcher; every inferred output retains real square rows."""
    def __init__(self, roles):
        self.roles = boundary(roles)
        self.rows = {}
        self.normalized = {}
        self.products = {}
        self.requests = {}
        self.targets = set()
        self.last = -1
        self._refresh()

    def _request(self, role, left, right):
        if role in self.requests:
            if self.requests[role] != (left, right):
                raise relation.RelationError('final balance inferred operand changed')
            return
        self.requests[role] = (left, right)
        folded = next(((scalar, other) for scalar, other in ((left, right), (right, left))
                       if not scalar or len(scalar) == 1 and scalar[0][0] == 0), None)
        if folded:
            scalar, other = folded
            self.products[role] = dict(output=canonical((c, v * (scalar[0][1] if scalar else 0))
                                                       for c, v in other), rows=[])
        elif left == right:
            self.targets.add(left)
        else:
            minus = combine(left, right, -1)
            self.targets.update((minus, canonical((c, -v) for c, v in minus), combine(left, right)))

    def _refresh(self):
        r = self.roles
        self._request('sign', r['negative'], canonical((c, -2*v) for c, v in r['unsigned'][0]))
        if 'sign' not in self.products:
            return
        signed = (combine(r['unsigned'][0], self.products['sign']['output']), r['unsigned'][1])
        self.signed = signed
        self._request('xx', signed[0], r['blinded'][0])
        self._request('yy', signed[1], r['blinded'][1])
        self._request('sum', combine(*signed), combine(*r['blinded']))
        if not {'xx', 'yy'} <= self.products.keys():
            return
        self._request('xy', self.products['xx']['output'], self.products['yy']['output'])
        if not {'sum', 'xy'} <= self.products.keys():
            return
        xx, yy, total, xy = (self.products[key]['output'] for key in ('xx', 'yy', 'sum', 'xy'))
        self.numerator = (combine(combine(total, xx, -1), yy, -1), combine(yy, xx))
        dt = canonical((c, D*v) for c, v in xy)
        self.denominator = (combine(ONE, dt), combine(ONE, dt, -1))
        for n, d, q in zip(self.numerator, self.denominator, r['output']):
            minus = combine(q, d, -1)
            self.targets.update((minus, canonical((c, -v) for c, v in minus), combine(q, d)))
            # The assertion LC includes an inferred product pivot. Retain only
            # bounded linear rows touching the actual quotient/source support.
        self.quotient_support = {c for lc in (*self.numerator, *r['output']) for c, _ in lc}

    def _infer(self):
        changed = True
        while changed:
            changed = False
            for role, (left, right) in list(self.requests.items()):
                if role in self.products and not self.products[role]['rows']:
                    continue
                if left == right:
                    candidates = [(b, (i,)) for i, (a, b) in self.normalized.items() if a == left]
                else:
                    minus, plus = combine(left, right, -1), combine(left, right)
                    negative = canonical((c, -v) for c, v in minus)
                    candidates = [(canonical((c, v * pow(4, -1, relation.MODULUS))
                                             for c, v in combine(b, aux, -1)), (i, j))
                                  for i, (a, aux) in self.normalized.items() if a in (minus, negative)
                                  for j, (p, b) in self.normalized.items() if p == plus and i != j]
        # Actual compiler product materializations have a unique unit
                # pivot. Refuse affine/fused alternatives rather than guessing.
                occupied = {c for c, _ in left + right} | {0}
                candidates = list(dict.fromkeys((out, indices) for out, indices in candidates
                                  if len([c for c, v in out if v == 1 and c not in occupied]) == 1))
                if len(candidates) > 1:
                    raise relation.RelationError('final balance ambiguous original product: ' + role)
                if candidates:
                    out, indices = candidates[0]
                    old = self.products.get(role)
                    new = dict(output=out, rows=list(indices))
                    if old is not None and old != new:
                        raise relation.RelationError('final balance physical product changed')
                    if old is None:
                        self.products[role] = new
                        changed = True
            if changed:
                self._refresh()

    def observe(self, record):
        if not isinstance(record, dict) or set(record) != {'row', 'a', 'b'}:
            raise relation.RelationError('final balance original closed row')
        index = relation.natural(record['row'], 200770)
        if index <= self.last:
            raise relation.RelationError('final balance original row order')
        self.last = index
        for key in ('a', 'b'):
            relation.terms(record[key], 262144)
        raw = tuple(tuple((c, int(v, 16)) for c, v in record[key]) for key in ('a', 'b'))
        normal = tuple(canonical((0 if c == 200692 else c, v) for c, v in side) for side in raw)
        keep = (normal[0] in self.targets or
                raw == (canonical([(0, 1), (200692, -1)]), ()) or
                not normal[1] and bool({c for c, _ in normal[0]} & getattr(self, 'quotient_support', set())))
        if not keep:
            return
        if len(self.rows) >= 256:
            raise relation.RelationError('final balance original candidate bound256')
        self.rows[index], self.normalized[index] = record, normal
        self._infer()

    def finish(self, identity, readonly_lcs=()):
        if (identity.get('relation_digest'), identity.get('domain_size'), identity.get('stored_rows')) != (DIGEST, 262144, 200770):
            raise relation.RelationError('final balance full original identity required')
        if set(self.products) != {'sign', 'xx', 'yy', 'sum', 'xy'}:
            raise relation.RelationError('final balance lowering order/physical products unsupported')
        if not isinstance(readonly_lcs, (list, tuple)) or len(readonly_lcs) > 4096:
            raise relation.RelationError('final balance readonly LC inventory bound')
        for lc in readonly_lcs:
            if not isinstance(lc, (list, tuple)) or len(lc) > 4096:
                raise relation.RelationError('final balance readonly LC term bound')
            for term in lc:
                if not isinstance(term, (list, tuple)) or len(term) != 2:
                    raise relation.RelationError('final balance readonly LC term shape')
                relation.natural(term[0], 262144)
                if type(term[1]) is not int or not 0 < term[1] < relation.MODULUS:
                    raise relation.RelationError('final balance readonly LC coefficient')
        stages = []
        protected = {0, 1, 2, 6, 200692}
        for lc in (self.roles['negative'], *self.roles['unsigned'], *self.roles['blinded'], *readonly_lcs):
            if canonical(lc) != tuple(lc):
                raise relation.RelationError('final balance readonly LC canonical')
            protected.update(c for c, _ in lc)
        covered = set()
        owned = set()
        prior = set()
        for role in ('sign', 'xx', 'yy', 'sum', 'xy'):
            left, right = self.requests[role]
            out = self.products[role]['output']
            cert = arithmetic.product_certificate(left, right, out, self.normalized)
            if cert['kind'].startswith('folded_'):
                continue
            stage = arithmetic.product_completion_certificate(left, right, out, cert, self.normalized)
            if stage is None:
                raise relation.RelationError('final balance unsupported actual product constructor: ' + role)
            stages.append(dict(kind='product', role=role, **stage))
        for axis, (n, d, q) in enumerate(zip(self.numerator, self.denominator, self.roles['output'])):
            cert = arithmetic.quotient_certificate(n, d, q, self.normalized)
            stage = arithmetic.completion_certificate(cert, self.normalized)
            if stage is None:
                raise relation.RelationError('final balance unsupported actual quotient constructor')
            stages.append(dict(kind='quotient', role='quotient.' + str(axis), **stage))
        for stage in stages:
            writes = ({stage['output'], stage['auxiliary']} if stage['kind'] == 'product' else
                      {stage['quotient'], stage['product'], stage['auxiliary']})
            if writes & (protected | owned | prior) or covered & set(stage['rows']):
                raise relation.RelationError('final balance writes alias shared/prior row support')
            owned.update(writes)
            covered.update(stage['rows'])
            prior.update(c for i in stage['rows'] for lc in self.normalized[i] for c, _ in lc)
        links = [i for i, row in self.rows.items() if tuple(tuple((c, int(v, 16)) for c, v in row[k])
                     for k in ('a', 'b')) == (canonical([(0, 1), (200692, -1)]), ())]
        if len(links) != 1:
            raise relation.RelationError('final balance unique original copy row required')
        covered.update(links)
        return dict(identity=identity, parents={key: self.roles[key] for key in
                    ('variable_parent', 'blinding_parent', 'caller_parent')}, roles=self.roles,
                    signed=self.signed, numerator=self.numerator, denominator=self.denominator,
                    stages=stages, writes=sorted(owned), protected=sorted(protected),
                    selected_rows=[self.rows[i] for i in sorted(covered)],
                    scope='Exact final balance row algebra/owned writes only; qualified source roles, curve/legal denominators, native balance endpoint and full frame remain separate')


def extract_rows(stream, roles, readonly_lcs=()):
    """Root-only one replay; may share Matcher.observe with another row collector."""
    matcher = Matcher(roles)
    identity = relation.inspect(stream, DIGEST, row_observer=matcher.observe)
    if identity['source_public'] != [[1, 22734]] or identity['source_blocks'] != [[[1, 6]]]:
        raise relation.RelationError('final balance production original input layout required')
    return matcher.finish(identity, readonly_lcs)


def from_ingress(variable_parent, variable_pages, blinding_parent, blinding_pages,
                 caller_parent, caller_page, accepted_roles, signed, asset_base, blinding_base):
    """Reaccept genuine parents and tie the blinding to the committed caller LC.

    `asset_base` and `blinding_base` are the independently associated actual
    map/source and SDK VALUE_BLINDING parameter objects, respectively. Their
    native mathematical association is deliberately not inferred from hashes.
    """
    import hashlib
    from . import transfer_balance_variable as variable, transfer_balance_blinding_fixed as blinding
    from . import transfer_remaining_pages as remaining
    v = variable.inspect_pages(variable_parent, variable_pages, DIGEST, signed, asset_base)
    c = remaining.inspect_page(caller_parent, caller_page, 0, accepted_roles)
    if c['metadata']['relation_digest'] != DIGEST:
        raise relation.RelationError('final balance exact caller relation required')
    scalar = c['records']['caller', 'shared', 0][6]
    b = blinding.inspect_pages(blinding_parent, blinding_pages, blinding_base, scalar)
    vp, bp = v['chunks'][0], b['chunks'][0]
    def observed(ref, expressions):
        if ref[0] == 'native':
            return canonical([(0, ref[1])])
        if ref[1] not in expressions:
            raise relation.RelationError('final balance exact endpoint LC missing')
        return expressions[ref[1]]
    scalar_lc = observed(remaining.reference(scalar), c['observed'])
    from . import transfer_balance_input_layout as layout
    layout_role=layout.source_role(scalar,scalar_lc)
    negative = observed(vp['negative'], vp['derived'])
    unsigned = tuple(observed(ref, vp['derived']) for ref in vp['points']['output'])
    blinded = b['chunks'][-1]['points'][-1][2]
    output = tuple(observed(remaining.reference(ref), c['observed'])
                   for ref in c['records']['caller', 'balance', 0])
    roles = boundary(dict(relation_digest=DIGEST, variable_parent=v['parent_sha256'],
                          blinding_parent=b['parent_sha256'], caller_parent=hashlib.sha256(caller_parent).hexdigest(),
                          negative=negative, unsigned=unsigned, blinded=blinded, output=output))
    return dict(roles=roles, input_layout=layout_role, variable_raw_pages=v['raw_page_sha256'],
                blinding_raw_pages=b['raw_page_sha256'], caller_raw_page=c['metadata_sha256'],
                scope='Derivative exact source/LC association only; native parameter/curve/full Transfer joins OPEN')


def extract_actual(stream, variable_parent, variable_pages, blinding_parent, blinding_pages,
                   caller_parent, caller_page, accepted_roles, signed, asset_base, blinding_base,
                   readonly_lcs=()):
    """Root-only strict genuine ingress plus one full original relation replay."""
    ingress = from_ingress(variable_parent, variable_pages, blinding_parent, blinding_pages,
                           caller_parent, caller_page, accepted_roles, signed, asset_base, blinding_base)
    from .transfer_balance_shared_add import Matcher as SharedMatcher
    matcher = SharedMatcher(ingress['roles'])
    identity = relation.inspect(stream, DIGEST, row_observer=matcher.observe)
    if identity['source_public'] != [[1, 22734]] or identity['source_blocks'] != [[[1, 6]]]:
        raise relation.RelationError('final balance production original input layout required')
    result = matcher.finish(identity, readonly_lcs)
    result['raw_parent_views'] = {k: ingress[k] for k in
                                  ('variable_raw_pages', 'blinding_raw_pages', 'caller_raw_page')}
    return result
