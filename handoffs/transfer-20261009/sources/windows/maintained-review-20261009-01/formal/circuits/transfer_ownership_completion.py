"""Exact retained-row construction recipe for one variable-base window.

The caller supplies already accepted ownership metadata and its independently
replayed row selection. This plan owns real square/product/quotient pivots;
it supplies no denominator legality, target equality, or evidence promotion.
"""
from . import transfer_ownership as owner, transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, combine


def _square(input_lc, output_lc, certificate, normalized):
    indices = certificate['rows']
    if len(indices) != 1 or normalized[indices[0]] != (input_lc, output_lc):
        raise relation.RelationError('ownership completion exact square row')
    occupied = {0, *(column for column, _ in input_lc)}
    pivots = [column for column, value in output_lc if value == 1 and column not in occupied]
    if len(pivots) != 1:
        raise relation.RelationError('ownership completion unique fresh square pivot')
    pivot = pivots[0]
    remainder = tuple(term for term in output_lc if term[0] != pivot)
    return dict(kind='square', input=input_lc, output=pivot,
                remainder=remainder, rows=indices)


def window_plan(checked, extracted, window_offset=0, include_precompute=True, readonly_lcs=()):
    """Bounded source order and exact local physical ownership, not a proof.

    The first two point operations precompute2/3base; each window then performs
    double, double, select/add. Source graphs are rechecked by existing formula
    certificates. Shared constants/bit/base roles stay outside all fresh writes.
    Other windows, endpoint assertions, and RNK nonidentity rows are explicitly
    outside this local plan and must be joined by their own constructors.
    """
    if type(window_offset) is not int or type(include_precompute) is not bool:
        raise relation.RelationError('ownership completion typed window selection')
    cones = owner.cone_certificates(checked, extracted, window_offset, include_precompute)
    quotients = owner.quotient_certificates(checked, extracted, window_offset, include_precompute)
    metadata = checked['metadata'];copy = metadata['constant_copy']
    if not isinstance(readonly_lcs, (tuple, list)) or len(readonly_lcs) > 4096:
        raise relation.RelationError('ownership completion bounded readonly roles')
    protected = {0, copy}
    for terms in readonly_lcs:
        if not isinstance(terms, (tuple, list)) or len(terms) > 4096:
            raise relation.RelationError('ownership completion canonical readonly roles')
        for term in terms:
            if not isinstance(term, (tuple, list)) or len(term) != 2:
                raise relation.RelationError('ownership completion readonly term shape')
            column, coefficient = term
            relation.natural(column, metadata['domain_size'])
            if type(coefficient) is not int or not 0 < coefficient < relation.MODULUS:
                raise relation.RelationError('ownership completion readonly coefficient')
            protected.add(column)
        if canonical(terms) != tuple(map(tuple, terms)):
            raise relation.RelationError('ownership completion canonical readonly roles')
    raw = {};normalized = {};previous = -1
    for row in extracted['selected_rows']:
        index = relation.natural(row['row'], metadata['full_rows'])
        if index <= previous:
            raise relation.RelationError('ownership completion ordered exact rows')
        previous = index
        raw[index] = tuple(tuple((c, int(v, 16)) for c, v in row[key]) for key in ('a', 'b'))
        normalized[index] = tuple(canonical((0 if c == copy else c, v) for c, v in terms)
                                  for terms in raw[index])
    observed = lambda value: checked['derived'][value[1]] if value[0] == 'source' else canonical([(0, value[1])])
    for point in (checked['points']['base'], checked['windows'][window_offset][0]):
        for handle in point:
            protected.update(column for column, _ in observed(handle))
    if not include_precompute:
        for point in (checked['points']['twice'], checked['points']['triple']):
            for handle in point:
                protected.update(column for column, _ in observed(handle))
    for handle in checked['bits']:
        protected.update(column for column, _ in checked['derived'][handle])
    cone_by_role = {cone['role']: cone for cone in cones['cones']}
    quotient_by_role = {certificate['role']: certificate for certificate in quotients['certificates']}
    stages = [];owned = set();covered = set();read_support = set();seen = set();folded = []
    unique_stages = {}
    def append(stage, role):
        writes = ({stage['output']} if stage['kind'] in ('square', 'linear') else
                  {stage['output'], stage['auxiliary']} if stage['kind'] == 'product' else
                  {stage['quotient'], stage['product'], stage['auxiliary']})
        # Repeated source cones may name the identical materialization. Reuse
        # requires identical operand/pivot/physical-row records, not a hash.
        key = tuple(stage['rows'])
        if key in unique_stages:
            if unique_stages[key] != stage:
                raise relation.RelationError('ownership completion inconsistent shared materialization')
            return
        if writes & (protected | owned | read_support):
            raise relation.RelationError('ownership completion write aliases shared/prior support: '+role)
        if covered & set(stage['rows']):
            raise relation.RelationError('ownership completion original row ownership overlap')
        unique_stages[key] = dict(stage);owned.update(writes);covered.update(stage['rows'])
        stages.append(dict(role=role, **stage))
        for index in stage['rows']:
            read_support.update(column for terms in normalized[index] for column, _ in terms)
    def emit_cone(index):
        cone = cone_by_role['formula'+str(index)]
        for identity in cone['ordered']:
            certificate = cone['certificates'][identity]
            if certificate['kind'] == 'input' or identity in seen:
                continue
            node = cone['source'][identity];output = cones['observations'][identity][1]
            if node['kind'] == 'constant':
                if output != canonical([(0, node['value'])]):
                    raise relation.RelationError('ownership completion constant source LC')
            else:
                left, right = (cones['observations'][node[side]][1] for side in ('left', 'right'))
                if node['kind'] == 'add':
                    if output != combine(left, right):
                        raise relation.RelationError('ownership completion add source LC')
                elif certificate['kind'].startswith('folded_'):
                    arithmetic.product_certificate(left, right, output, normalized)
                    folded.append(identity)
                elif certificate['kind'] == 'square':
                    matches = [i for i, row in normalized.items() if row == (left, output)]
                    if matches != certificate['rows']:
                        raise relation.RelationError('ownership completion unique square physical row')
                    append(_square(left, output, certificate, normalized), identity)
                else:
                    difference = combine(left, right, -1);total = combine(left, right)
                    matches = [(i, j) for i, row in normalized.items() if row[0] == difference
                               for j, other in normalized.items()
                               if other == (total, combine(row[1], output, 4))]
                    if matches != [tuple(certificate['rows'])]:
                        raise relation.RelationError('ownership completion unique product physical pair')
                    stage = arithmetic.product_completion_certificate(left, right, output, certificate, normalized)
                    if stage is None:
                        raise relation.RelationError('ownership completion exact product pivots')
                    append(dict(kind='product', **stage), identity)
            seen.add(identity)
    def emit_quotient(index):
        for axis in range(2):
            role = f'quotient.{index}.{axis}';certificate = quotient_by_role[role]
            if certificate['kind'] == 'folded':
                if (not certificate['rows'] and certificate['denominator'] == ((0, 1),)
                        and certificate['quotient'] == certificate['numerator']):
                    folded.append(role);continue
                stage = arithmetic.folded_quotient_completion_certificate(certificate, normalized)
                kind = 'linear'
            else:
                stage = arithmetic.completion_certificate(certificate, normalized);kind = 'quotient'
            if stage is None:
                raise relation.RelationError('ownership completion unsupported quotient shape: '+role)
            append(dict(kind=kind, **stage), role)
    groups = [(0, 4, 0), (4, 4, 1)] if include_precompute else []
    start = 8+14*window_offset;point_index = 2+3*window_offset
    groups += [(start, 4, point_index), (start+4, 4, point_index+1), (start+8, 6, point_index+2)]
    point_groups = []
    for first, count, quotient in groups:
        before = len(stages)
        # Runtime selects the affine window point before adding it. Its source
        # LC can name materialized selector products even when the addition
        # graph treats that LC as an input. Construct those actual products
        # first; retain every prior/shared-support freshness check below.
        order = (list(range(first+4, first+6)) + list(range(first, first+4))
                 if count == 6 else range(first, first+count))
        for index in order:emit_cone(index)
        material_end = len(stages)
        emit_quotient(quotient)
        point_groups.append(dict(index=quotient, formula_start=first,
                                 formula_count=count, stage_start=before,
                                 material_end=material_end, stage_end=len(stages),
                                 kind='add' if count==6 or quotient==1 else 'double'))
    link_rows = [index for index, row in raw.items()
                 if row == (canonical([(0, 1), (copy, -1)]), ())]
    if len(link_rows) != 1:
        raise relation.RelationError('ownership completion unique constant copy')
    demanded = set(cones['rows']) | set(quotients['rows'])
    if covered | set(link_rows) != demanded:
        raise relation.RelationError('ownership completion every local materialization row covered')
    return dict(window_index=metadata['window_start']+window_offset,
                include_precompute=include_precompute, stages=stages, writes=sorted(owned),
                protected=sorted(protected), folded=folded, point_groups=point_groups,
                local_rows=sorted(demanded), constant_rows=link_rows,
                outside_scope_rows=sorted(set(raw)-demanded),
                scope='retained exact local variable-window ownership recipe only; source acceptance/replay/kernel/denominator/endpoint/native joins separate')
