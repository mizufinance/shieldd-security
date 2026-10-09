"""Actual balance Point<Var>::add shared-inverse lowering.

This follows group.rs Point<F>::add, not the affine window helper. Every
intermediate is inferred from original compiler rows; missing, ambiguous or
aliased materializations refuse. A retained plan is not a qualification.
"""
from . import transfer_balance_final_add as final, transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, combine

PRODUCT_ORDER = ('sign', 'xx', 'yy', 'xy', 'denominator', 'crossX', 'crossY',
                 'xMinus', 'xOutput', 'yPlus', 'yOutput')


def reciprocal_completion(certificate, normalized):
    """Construct the exact retained reciprocal through signed A transport.

    Var::assert_eq may emit numerator minus product. Squared-row A permits
    either sign; B must remain identical. The original rows stay untouched
    and the renderer separately checks their signed canonical coverage.
    """
    if certificate.get('kind') != 'product' or len(certificate.get('rows', ())) != 3:
        return None
    q, den = certificate['quotient'], certificate['denominator']
    out, aux = certificate['output'], certificate['auxiliary']
    expected = [(combine(q, den, -1), aux),
                (combine(q, den), combine(aux, out, 4)),
                (combine(out, certificate['numerator'], -1), ())]
    canonical_rows = dict(normalized)
    for index, (a, b) in zip(certificate['rows'], expected):
        actual_a, actual_b = normalized[index]
        if actual_b != b or actual_a not in (a, canonical((c, -v) for c, v in a)):
            return None
        canonical_rows[index] = a, b
    return arithmetic.completion_certificate(dict(certificate, swapped=False), canonical_rows)


class Matcher(final.Matcher):
    def _refresh(self):
        r = self.roles
        self._request('sign', r['negative'], canonical((c, -2*v) for c, v in r['unsigned'][0]))
        if 'sign' not in self.products:
            return
        self.signed = (combine(r['unsigned'][0], self.products['sign']['output']), r['unsigned'][1])
        self._request('xx', self.signed[0], r['blinded'][0])
        self._request('yy', self.signed[1], r['blinded'][1])
        if not {'xx', 'yy'} <= self.products.keys():
            return
        self._request('xy', self.products['xx']['output'], self.products['yy']['output'])
        if 'xy' not in self.products:
            return
        self.delta = canonical((c, final.D*v) for c, v in self.products['xy']['output'])
        self.plus, self.minus = combine(final.ONE, self.delta), combine(final.ONE, self.delta, -1)
        self._request('denominator', self.plus, self.minus)
        if 'denominator' not in self.products:
            return
        self.inverse_denominator = self.products['denominator']['output']
        inverse = getattr(self, 'inverse', None)
        if inverse is None:
            return
        self._request('inverseProduct', inverse, self.inverse_denominator)
        self._request('crossX', self.signed[0], r['blinded'][1])
        self._request('crossY', self.signed[1], r['blinded'][0])
        if {'crossX', 'crossY'} <= self.products.keys():
            self.cross = combine(self.products['crossX']['output'], self.products['crossY']['output'])
            self._request('xMinus', self.cross, self.minus)
        if 'xMinus' in self.products:
            self._request('xOutput', self.products['xMinus']['output'], inverse)
        self.diagonal = combine(self.products['yy']['output'], self.products['xx']['output'])
        self._request('yPlus', self.diagonal, self.plus)
        if 'yPlus' in self.products:
            self._request('yOutput', self.products['yPlus']['output'], inverse)

    def _inverse_candidate(self, left):
        denominator = getattr(self, 'inverse_denominator', None)
        if denominator is None:
            return None
        protected = {0, 1, 2, 6, 200692} | {c for lc in
            (self.roles['negative'], *self.roles['unsigned'], *self.roles['blinded'], denominator)
            for c, _ in lc}
        candidates = {canonical((c, sign*v) for c, v in combine(left, denominator, den_sign))
                      for sign in (1, -1) for den_sign in (1, -1)}
        candidates = {q for q in candidates if len(q) == 1 and q[0][1] == 1 and q[0][0] not in protected}
        if len(candidates) > 1:
            raise relation.RelationError('final shared inverse ambiguous original operand')
        return next(iter(candidates), None)

    def _infer(self):
        changed = True
        while changed:
            changed = False
            if not hasattr(self, 'inverse') and hasattr(self, 'inverse_denominator'):
                candidates = {q for a, _ in self.normalized.values() if (q := self._inverse_candidate(a)) is not None}
                if len(candidates) > 1:
                    raise relation.RelationError('final shared inverse ambiguous original witness')
                if candidates:
                    self.inverse = candidates.pop()
                    self._refresh()
                    changed = True
            for role, (left, right) in list(self.requests.items()):
                if role in self.products:
                    continue
                if left == right:
                    candidates = [(b, (i,)) for i, (a, b) in self.normalized.items() if a == left]
                else:
                    minus, plus = combine(left, right, -1), combine(left, right)
                    negative = canonical((c, -v) for c, v in minus)
                    candidates = [(canonical((c, v*pow(4, -1, relation.MODULUS))
                                      for c, v in combine(b, aux, -1)), (i, j))
                                  for i, (a, aux) in self.normalized.items() if a in (minus, negative)
                                  for j, (p, b) in self.normalized.items() if p == plus and i != j]
                occupied = {c for c, _ in left + right} | {0}
                # compile_product allocates exactly one output column. Requiring
                # it prevents cross-pairing unrelated constant-sum square rows.
                candidates = list(dict.fromkeys((out, indices) for out, indices in candidates
                    if len(out) == 1 and out[0][1] == 1 and out[0][0] not in occupied))
                if len(candidates) > 1:
                    raise relation.RelationError('final shared inverse ambiguous product: ' + role)
                if candidates:
                    out, indices = candidates[0]
                    self.products[role] = dict(output=out, rows=list(indices))
                    self._refresh()
                    changed = True

    def observe(self, record):
        if not isinstance(record, dict) or set(record) != {'row', 'a', 'b'}:
            raise relation.RelationError('final shared inverse original closed row')
        index = relation.natural(record['row'], 200770)
        if index <= self.last:
            raise relation.RelationError('final shared inverse original row order')
        self.last = index
        for key in ('a', 'b'):
            relation.terms(record[key], 262144)
        raw = tuple(tuple((c, int(v, 16)) for c, v in record[key]) for key in ('a', 'b'))
        normal = tuple(canonical((0 if c == 200692 else c, v) for c, v in side) for side in raw)
        inverse_candidate = self._inverse_candidate(normal[0])
        assertion_support = {c for item in self.products.values() for c, _ in item['output']}
        keep = (normal[0] in self.targets or inverse_candidate is not None or
                raw == (canonical([(0, 1), (200692, -1)]), ()) or
                not normal[1] and bool({c for c, _ in normal[0]} & assertion_support))
        if keep:
            if len(self.rows) >= 256:
                raise relation.RelationError('final shared inverse original candidate bound256')
            self.rows[index], self.normalized[index] = record, normal
            self._infer()

    def finish(self, identity, readonly_lcs=()):
        if (identity.get('relation_digest'), identity.get('domain_size'), identity.get('stored_rows')) != (
                final.DIGEST, 262144, 200770):
            raise relation.RelationError('final shared inverse full original identity required')
        if set(self.products) != set(PRODUCT_ORDER) | {'inverseProduct'}:
            raise relation.RelationError('final shared inverse missing physical product: ' +
                ','.join(sorted((set(PRODUCT_ORDER) | {'inverseProduct'}) - self.products.keys())))
        if tuple(self.products[role]['output'] for role in ('xOutput', 'yOutput')) != self.roles['output']:
            raise relation.RelationError('final shared inverse actual output LC differs from source')
        if not isinstance(readonly_lcs, (list, tuple)) or len(readonly_lcs) > 4096:
            raise relation.RelationError('final shared inverse bounded readonly inventory')
        protected = {0, 1, 2, 6, 200692}
        for lc in (self.roles['negative'], *self.roles['unsigned'], *self.roles['blinded'], *readonly_lcs):
            if not isinstance(lc, (list, tuple)) or len(lc) > 4096:
                raise relation.RelationError('final shared inverse readonly LC bound')
            for c, v in lc:
                relation.natural(c, 262144)
                if type(v) is not int or not 0 < v < relation.MODULUS:
                    raise relation.RelationError('final shared inverse readonly coefficient')
            if canonical(lc) != tuple(lc):
                raise relation.RelationError('final shared inverse readonly canonical LC')
            protected.update(c for c, _ in lc)
        stages = []
        for role in PRODUCT_ORDER:
            left, right = self.requests[role]
            output = self.products[role]['output']
            cert = arithmetic.product_certificate(left, right, output, self.normalized)
            if cert['kind'].startswith('folded_'):
                continue
            stage = arithmetic.product_completion_certificate(left, right, output, cert, self.normalized)
            if stage is None:
                raise relation.RelationError('final shared inverse unsupported product constructor: ' + role)
            stages.append(dict(kind='product', role=role, **stage))
        inverse_cert = arithmetic.quotient_certificate(final.ONE, self.inverse_denominator, self.inverse, self.normalized)
        inverse_stage = reciprocal_completion(inverse_cert, self.normalized)
        if inverse_stage is None:
            raise relation.RelationError('final shared inverse unsupported reciprocal constructor')
        pivot = next(i for i, stage in enumerate(stages) if stage['role'] == 'denominator')
        stages.insert(pivot + 1, dict(kind='quotient', role='inverse', **inverse_stage))
        covered, owned, prior = set(), set(), set()
        for stage in stages:
            writes = ({stage['output'], stage['auxiliary']} if stage['kind'] == 'product' else
                      {stage['quotient'], stage['product'], stage['auxiliary']})
            if writes & (protected | owned | prior) or covered & set(stage['rows']):
                raise relation.RelationError('final shared inverse writes alias shared/prior row support')
            owned.update(writes); covered.update(stage['rows'])
            prior.update(c for i in stage['rows'] for lc in self.normalized[i] for c, _ in lc)
        links = [i for i, row in self.rows.items() if tuple(tuple((c, int(v, 16)) for c, v in row[k])
                  for k in ('a', 'b')) == (canonical([(0, 1), (200692, -1)]), ())]
        if len(links) != 1:
            raise relation.RelationError('final shared inverse unique copied constant row')
        covered.update(links)
        return dict(lowering='point_shared_inverse', identity=identity,
                    parents={k: self.roles[k] for k in ('variable_parent', 'blinding_parent', 'caller_parent')},
                    roles=self.roles, signed=self.signed, inverse=self.inverse,
                    plus=self.plus, minus=self.minus, cross=self.cross, diagonal=self.diagonal,
                    stages=stages, writes=sorted(owned), protected=sorted(protected),
                    selected_rows=[self.rows[i] for i in sorted(covered)],
                    scope='Exact native Point<Var>::add shared-inverse original rows only; legal curve/global parameters and earlier native source joins remain independent.')
