"""Actual computed/RK equality rows, with no randomizer or signature claims.

Accepted caller metadata supplies the two captured source LCs. Only the exact
ordinary relation stream can supply their equality rows. Full fixed-window,
canonical-randomizer, RK subgroup/nonidentity and native/caller joins are open.
Generated Lean is a diagnostic candidate until separately kernel checked.
"""
import hashlib

from . import transfer_authorization_roles as roles, transfer_relation as relation
from .transfer_balance_rows import canonical, combine, source_index
from .generate_hash_round import linear, _signature_audits

P = relation.MODULUS
SCOPE = 'actual computed/RK equality extraction only; fixed windows, canonical randomizer, RK subgroup/nonidentity, native and caller joins open'


def _captured_pair(value, domain):
    """Strictly normalize integer LCs, including persisted JSON arrays."""
    if not isinstance(value, (list, tuple)) or len(value) != 2:
        raise relation.RelationError('malformed RK binding captured point LC')
    result = []
    for axis in value:
        if not isinstance(axis, (list, tuple)) or len(axis) > 4096:
            raise relation.RelationError('RK binding captured coordinate LC bound')
        terms = []
        previous = -1
        for term in axis:
            if not isinstance(term, (list, tuple)) or len(term) != 2:
                raise relation.RelationError('malformed RK binding captured LC term')
            column = relation.natural(term[0], domain)
            coefficient = term[1]
            if column <= previous or type(coefficient) is not int or not 0 < coefficient < P:
                raise relation.RelationError('noncanonical RK binding captured LC term')
            previous = column
            terms.append((column, coefficient))
        result.append(tuple(terms))
    return tuple(result)


def _boundary(data, expected_relation, ivk_handles, rnk, ivk):
    checked = roles.inspect_metadata(data, expected_relation, ivk_handles, rnk, ivk)
    obj, observed = checked['metadata'], checked['observed']
    spend = obj['spend']
    values = {name: tuple(observed[source_index(value['source'])] for value in spend[name])
              for name in ('computed', 'rk')}
    copy = obj['constant_copy']

    def outlined(terms):
        return canonical((copy if column == 0 else column, value) for column, value in terms)

    wanted = {'constant-copy': (canonical([(0, 1), (copy, -1)]), ())}
    for axis, left, right in zip(('x', 'y'), values['computed'], values['rk']):
        difference = outlined(combine(left, right, -1))
        if not difference:
            raise relation.RelationError('RK binding must have a nontrivial captured equality: ' + axis)
        wanted[axis] = (difference, ())
    return checked, values, wanted


def extract(data, stream, expected_relation, ivk_handles, rnk, ivk):
    """Reaccept roles and match original rows while checking the full digest.

    No actual roles are invented when a capture is absent. Accepted RNK-DH/IVK
    metadata inputs keep the same preconditions as the role ingress.
    """
    checked, values, wanted = _boundary(data, expected_relation, ivk_handles, rnk, ivk)
    matched, selected, orientations = {}, {}, {}

    def observe(row):
        key = tuple((column, int(value, 16)) for column, value in row['a']), tuple(
            (column, int(value, 16)) for column, value in row['b'])
        for name, target in wanted.items():
            if name in matched:
                continue
            inverse = (canonical((column, -value) for column, value in target[0]), ())
            if key == target or (name != 'constant-copy' and key == inverse):
                matched[name] = row['row']
                selected[row['row']] = row
                if name != 'constant-copy':
                    orientations[name] = 'computed-minus-rk' if key == target else 'rk-minus-computed'

    identity = relation.inspect(stream, expected_relation=expected_relation, row_observer=observe)
    obj = checked['metadata']
    if identity['domain_size'] != obj['domain_size'] or identity['stored_rows'] != obj['full_rows']:
        raise relation.RelationError('RK binding metadata/full relation shape mismatch')
    missing = set(wanted) - set(matched)
    if missing:
        raise relation.RelationError('missing actual RK binding row: ' + sorted(missing)[0])
    return dict(identity=identity, metadata_sha256=hashlib.sha256(data).hexdigest(),
                roles=matched, orientations=orientations, constant_copy=obj['constant_copy'],
                computed=values['computed'], rk=values['rk'],
                selected_rows=[selected[index] for index in sorted(selected)], scope=SCOPE)


def _selection(data, extracted, expected_relation, ivk_handles, rnk, ivk):
    """Fail closed before generating from a supplied extraction result."""
    checked, values, wanted = _boundary(data, expected_relation, ivk_handles, rnk, ivk)
    obj = checked['metadata']
    if not isinstance(extracted, dict) or extracted.get('metadata_sha256') != hashlib.sha256(data).hexdigest():
        raise relation.RelationError('RK binding extraction metadata identity mismatch')
    identity = extracted.get('identity')
    if not isinstance(identity, dict) or (identity.get('relation_digest') != expected_relation or
            relation.natural(identity.get('domain_size')) != obj['domain_size'] or
            relation.natural(identity.get('stored_rows')) != obj['full_rows']):
        raise relation.RelationError('RK binding extraction relation identity mismatch')
    if (relation.natural(extracted.get('constant_copy'), obj['domain_size']) != obj['constant_copy'] or
            _captured_pair(extracted.get('computed'), obj['domain_size']) != values['computed'] or
            _captured_pair(extracted.get('rk'), obj['domain_size']) != values['rk']):
        raise relation.RelationError('RK binding extraction captured LC mismatch')
    if not isinstance(extracted.get('roles'), dict) or set(extracted['roles']) != set(wanted):
        raise relation.RelationError('RK binding extraction role inventory mismatch')
    if not isinstance(extracted.get('orientations'), dict) or set(extracted['orientations']) != {'x', 'y'}:
        raise relation.RelationError('RK binding extraction orientation inventory mismatch')
    records = extracted.get('selected_rows')
    if not isinstance(records, list) or not 1 <= len(records) <= 3:
        raise relation.RelationError('RK binding selected row bound')
    rows = {}
    previous = -1
    for row in records:
        if not isinstance(row, dict) or set(row) != {'row', 'a', 'b'}:
            raise relation.RelationError('malformed RK binding selected row')
        index = relation.natural(row['row'], obj['full_rows'])
        if index <= previous:
            raise relation.RelationError('RK binding selected rows unordered/duplicate')
        previous = index
        relation.terms(row['a'], obj['domain_size'])
        relation.terms(row['b'], obj['domain_size'])
        rows[index] = tuple((column, int(value, 16)) for column, value in row['a']), tuple(
            (column, int(value, 16)) for column, value in row['b'])
    indices = set()
    for name, target in wanted.items():
        index = relation.natural(extracted['roles'][name], obj['full_rows'])
        indices.add(index)
        if name != 'constant-copy':
            orientation = extracted['orientations'][name]
            if orientation not in ('computed-minus-rk', 'rk-minus-computed'):
                raise relation.RelationError('unknown RK binding orientation')
            if orientation == 'rk-minus-computed':
                target = canonical((column, -value) for column, value in target[0]), ()
        if rows.get(index) != target:
            raise relation.RelationError('RK binding selected semantic row mismatch: ' + name)
    if indices != set(rows):
        raise relation.RelationError('RK binding selected row coverage mismatch')
    return checked, values, rows


def generate(data, extracted, expected_relation, ivk_handles, rnk, ivk):
    """Return a finite three-row diagnostic theorem candidate, never publish."""
    checked, values, rows = _selection(data, extracted, expected_relation, ivk_handles, rnk, ivk)
    obj = checked['metadata']
    source = f'''import ShielddSecurity.Group
set_option maxHeartbeats 200000
namespace ShielddSecurity.RuntimeTransferRkBinding
-- Exact relation: {expected_relation}
-- Caller metadata SHA256 (byte identity only): {extracted['metadata_sha256']}
-- Original selected rows: {sorted(rows)}
-- Computed/RK equality only; randomizer, fixed windows and native joins OPEN.
def modulus : Nat := {P}
def rawRows : List Row := [
'''
    source += ',\n'.join('  ⟨' + linear(a) + ', ' + linear(b) + '⟩' for a, b in rows.values()) + ']\n'
    source += f'def rows : List Row := Compiler.unoutlineRows {obj["constant_copy"]} rawRows\n'
    for name in ('computed', 'rk'):
        for axis, terms in zip(('X', 'Y'), values[name]):
            source += f'def {name}{axis} : Linear := {linear(terms)}\n'
        source += f'''def {name} {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {name}X,eval rho {name}Y⟩
'''
    source += f'''theorem constantLink : Compiler.checkRow modulus rawRows
    ⟨[(0,1),({obj['constant_copy']},-1)],[]⟩ = true := by decide
'''
    for axis in ('x', 'y'):
        coordinate = axis.upper()
        left, right = 'computed' + coordinate, 'rk' + coordinate
        reverse = extracted['orientations'][axis] == 'rk-minus-computed'
        proof_left, proof_right = (right, left) if reverse else (left, right)
        source += f'''theorem rk_{axis}_equal {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho {left} = eval rho {right} := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {obj['constant_copy']} rawRows satisfied constantLink
  exact (Compiler.checked_assertion_sound rho rows {proof_left} {proof_right}
    normalized (by decide)){'.symm' if reverse else ''}
'''
    source += '''theorem actual_rk_binding {F : Type} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) : computed rho = rk rho := by
  exact congrArg₂ Group.Point.mk (rk_x_equal rho satisfied) (rk_y_equal rho satisfied)
#print axioms constantLink
#print axioms rk_x_equal
#print axioms rk_y_equal
#print axioms actual_rk_binding
end ShielddSecurity.RuntimeTransferRkBinding
'''
    return _signature_audits(source)
