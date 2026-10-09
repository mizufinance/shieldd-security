"""Bounded exact LC substitution for reused owned arithmetic templates.

A substitution alone proves nothing. The kernel must check all source rows,
input/output roles, and transport their satisfaction under the induced assignment.
Aliased images are valid for soundness; constructor freshness is a separate claim.
"""
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, combine


def linear(terms, columns):
    result = []
    for column, factor in terms:
        if column not in columns:
            raise relation.RelationError('LC substitution missing source column')
        result.extend((actual, factor * coefficient) for actual, coefficient in columns[column])
    return canonical(result)


def infer(pairs, row_pairs, source_rows, actual_rows, *, source_copy, actual_copy):
    """Solve only one missing expression at a time; check every matched row.

    Each step has one unique field-valued LC solution. Multiple unknowns are
    refused rather than assigned an arbitrary correspondence. Inputs should be
    exact bounded formula/compiler role pairs from independently parsed captures.
    """
    if (not isinstance(pairs, list) or not 0 < len(pairs) <= 8192 or
            not isinstance(row_pairs, list) or not 0 < len(row_pairs) <= 8192 or
            not isinstance(source_rows, dict) or not isinstance(actual_rows, dict) or
            not 0 < len(source_rows) <= 8192 or not 0 < len(actual_rows) <= 8192 or
            type(source_copy) is not int or source_copy < 3 or
            source_copy >= 2**32 or type(actual_copy) is not int or not 3 <= actual_copy < 2**32):
        raise relation.RelationError('LC substitution bounded collections/copy columns')
    if (any(not isinstance(pair, (tuple, list)) or len(pair) != 2 for pair in pairs + row_pairs) or
            any(type(index) is not int or not 0 <= index < 2**32 or
                not isinstance(row, (tuple, list)) or len(row) != 2
                for rows in (source_rows, actual_rows) for index, row in rows.items())):
        raise relation.RelationError('LC substitution pair/physical-row shape')
    term_count = 0

    def checked(terms):
        nonlocal term_count
        if (not isinstance(terms, (tuple, list)) or len(terms) > 4096 or
                any(not isinstance(term, (tuple, list)) or len(term) != 2 or
                    type(term[0]) is not int or not 0 <= term[0] < 2**32 or
                    type(term[1]) is not int for term in terms)):
            raise relation.RelationError('LC substitution canonical term shape')
        term_count += len(terms)
        if term_count > 262144:
            raise relation.RelationError('LC substitution total term bound')
        return canonical(terms)

    pending = [(checked(left), checked(right)) for left, right in pairs]
    source_rows = {index: tuple(checked(terms) for terms in row) for index, row in source_rows.items()}
    actual_rows = {index: tuple(checked(terms) for terms in row) for index, row in actual_rows.items()}
    if any(len(row) != 2 for row in [*source_rows.values(), *actual_rows.values()]):
        raise relation.RelationError('LC substitution two-expression row shape')
    columns = {0: ((0, 1),), source_copy: ((actual_copy, 1),)}
    for _ in range(256):
        progress, remaining = False, []
        for left, right in pending:
            known = linear([(column, factor) for column, factor in left if column in columns], columns)
            residual = combine(right, known, -1)
            missing = [(column, factor) for column, factor in left if column not in columns]
            if not missing:
                if residual:
                    raise relation.RelationError('LC substitution role equality mismatch')
            elif len(missing) == 1:
                column, factor = missing[0]
                inverse = pow(factor, -1, relation.MODULUS)
                columns[column] = canonical((actual, coefficient * inverse) for actual, coefficient in residual)
                progress = True
            else:
                remaining.append((left, right))
        pending = remaining
        if not pending:
            break
        if not progress:
            raise relation.RelationError('LC substitution ambiguous expression correspondence')
    if pending:
        raise relation.RelationError('LC substitution finite inference bound')
    targets = {}
    for original, actual in row_pairs:
        if original not in source_rows or actual not in actual_rows:
            raise relation.RelationError('LC substitution missing physical row')
        if original in targets and targets[original] != actual:
            raise relation.RelationError('LC substitution row correspondence conflict')
        targets[original] = actual
        renamed = tuple(linear(terms, columns) for terms in source_rows[original])
        wanted = actual_rows[actual]
        if renamed not in (wanted, (canonical((column, -factor) for column, factor in wanted[0]), wanted[1])):
            raise relation.RelationError('LC substitution actual row mismatch')
    if set(targets) != set(source_rows):
        raise relation.RelationError('LC substitution omitted template row')
    return dict(columns=sorted(columns.items()), row_targets=sorted(targets.items()),
                source_rows=source_rows, actual_rows=actual_rows,
                scope='Exact bounded LC/row correspondence only; kernel satisfaction and role transport/freshness remain required')
