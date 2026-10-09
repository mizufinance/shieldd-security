"""Find the actual issuer x-inverse rows without inventing observer handles.

Three full ordinary replays first locate =1 assertions, then propose bounded
single-column inverses from their materializations, then check complete products.
Unrelated point products never consume the inverse candidate budget. Source/caller association,
native parameters and constructive write ownership remain separate obligations.
"""
from . import transfer_relation as relation, transfer_arithmetic as arithmetic
from .transfer_encryption_dh_keys import infer_regulated_selectors
from .transfer_balance_rows import canonical, combine
from .generate_hash_round import linear, _signature_audits


def _unit(value):
    return len(value) == 1 and value[0][0] != 0 and value[0][1] == 1


def extract(checked, open_stream):
    obj = checked.get('metadata', {})
    if (checked.get('qualified') is not True or obj.get('schema') != 'shieldd-transfer-encryption-dh-v1'
            or type(obj.get('role')) is not int or obj['role'] != 0):
        raise relation.RelationError('DH issuer inverse qualified first occurrence required')
    infer_regulated_selectors(checked)
    handles = checked['bindings']['detection_key']
    point = tuple(checked['derived'][value[1]] if value[0] == 'source'
                  else canonical([(0, value[1])]) for value in handles)
    x = point[0]
    if not x or all(c == 0 for c, _ in x):
        raise relation.RelationError('DH issuer inverse expects actual nonconstant selected x')
    copy = obj['constant_copy']
    records, candidates, asserted = {}, set(), set()
    link = (canonical([(0, 1), (copy, -1)]), ())
    links = []

    def normalize(row):
        return tuple(canonical((0 if c == copy else c, int(v, 16)) for c, v in row[key])
                     for key in ('a', 'b'))

    def retain(row):
        records[row['row']] = row
        if len(records) > 4096:
            raise relation.RelationError('DH issuer inverse retained row4096 bound')

    def observe_first(row):
        raw = tuple(tuple((c, int(v, 16)) for c, v in row[key]) for key in ('a', 'b'))
        a, b = normalize(row)
        if raw == link:
            links.append(row['row'])
            retain(row)
        if not b:
            for output in (combine(a, ((0, 1),)), combine(((0, 1),), a, -1)):
                if _unit(output):
                    asserted.add(output[0][0])
                    retain(row)
    with open_stream() as stream:
        first = relation.inspect(stream, expected_relation=obj['relation_digest'], row_observer=observe_first)
    if first['domain_size'] != obj['domain_size'] or first['stored_rows'] != obj['full_rows']:
        raise relation.RelationError('DH issuer inverse ordinary shape mismatch')
    if len(links) != 1 or not asserted:
        raise relation.RelationError('DH issuer inverse unique constant link and assertion required')

    def observe_materialization(row):
        a, b = normalize(row)
        inverse = combine(a, x, -1)
        if not _unit(inverse) or inverse[0][0] in {c for c, _ in x}:
            return
        for column, coefficient in b:
            if coefficient == 4 and column in asserted:
                auxiliary = combine(b, ((column, 4),), -1)
                if _unit(auxiliary):
                    candidates.add(inverse)
                    retain(row)
                    if len(candidates) > 64:
                        raise relation.RelationError('DH issuer inverse candidate64 bound')
    with open_stream() as stream:
        materialized = relation.inspect(stream, expected_relation=obj['relation_digest'],
                                        row_observer=observe_materialization)
    if first != materialized:
        raise relation.RelationError('DH issuer inverse complete replay identity mismatch')
    if not candidates:
        raise relation.RelationError('DH issuer inverse asserted materialization candidate required')
    targets = {term for inverse in candidates for term in
               (combine(inverse, x, -1), combine(x, inverse, -1), combine(inverse, x))}

    def observe_second(row):
        a, _ = normalize(row)
        if a in targets:
            retain(row)
    with open_stream() as stream:
        second = relation.inspect(stream, expected_relation=obj['relation_digest'], row_observer=observe_second)
    if first != second:
        raise relation.RelationError('DH issuer inverse complete replay identity mismatch')
    normalized = {i: normalize(row) for i, row in records.items()}
    matches = []
    for inverse in sorted(candidates):
        try:
            cert = arithmetic.quotient_certificate(((0, 1),), x, inverse, normalized)
        except relation.RelationError:
            continue
        if cert['kind'] == 'product' and len(cert['rows']) == 3:
            matches.append(cert)
    if len(matches) != 1:
        raise relation.RelationError('DH issuer inverse one complete materialization/assertion required')
    cert = matches[0]
    indices = sorted(set(cert['rows']) | set(links))
    if len(indices) != 4:
        raise relation.RelationError('DH issuer inverse four distinct physical rows required')
    return dict(identity=first, metadata_sha256=checked.get('metadata_sha256'), point=point,
                certificate=cert, selected_rows=[records[i] for i in indices],
                scope='Actual selected detection x inverse product/=1 rows. Source caller/native '
                      'key parameter/legal write ownership and full Transfer OPEN')


def generate(checked, extracted):
    obj = checked['metadata']
    raw, normalized = arithmetic.normalize_selection(extracted, obj, checked['metadata_sha256'])
    infer_regulated_selectors(checked)
    point = tuple(checked['derived'][value[1]] if value[0] == 'source'
                  else canonical([(0, value[1])]) for value in checked['bindings']['detection_key'])
    if tuple(extracted['point']) != point:
        raise relation.RelationError('DH issuer inverse exact selected point source required')
    recorded = extracted['certificate']
    cert = arithmetic.quotient_certificate(((0, 1),), point[0], recorded['quotient'], normalized)
    if cert != recorded or cert['kind'] != 'product' or len(cert['rows']) != 3:
        raise relation.RelationError('DH issuer inverse exact rechecked quotient certificate required')
    name = 'RuntimeTransferEncryptionDetectionInverse'
    x, y = point
    inverse, product, auxiliary = map(linear, (cert['quotient'], cert['output'], cert['auxiliary']))
    source = f'''import ShielddSecurity.RowOrientationSoundness
import ShielddSecurity.GroupWindows
namespace ShielddSecurity.{name}
set_option maxHeartbeats 400000
def modulus : Nat := {relation.MODULUS}
def originalRows : List Nat := {sorted(raw)}
def rawRows : List Row := [
''' + ',\n'.join('  ⟨' + linear(a) + ', ' + linear(b) + '⟩' for a, b in raw.values()) + f''']
def unoutlined : List Row := Compiler.unoutlineRows {obj['constant_copy']} rawRows
def rows : List Row := unoutlined ++ unoutlined.map (fun row => ⟨scaleLinear (-1) row.a, row.b⟩)
def point {{F : Type}} [Field F] (rho : Nat → F) : Group.Point F :=
  ⟨eval rho {linear(x)}, eval rho {linear(y)}⟩
theorem link_checked : Compiler.checkRow modulus rawRows
    ⟨[(0,1),({obj['constant_copy']},-1)],[]⟩ = true := by decide
theorem rows_checked : rows.all (fun row => Compiler.checkRow modulus unoutlined row ||
    Compiler.checkRow modulus unoutlined ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide
theorem rows_satisfied {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) : Satisfies rho rows := by
  have original := Compiler.unoutline_rows_sound rho {obj['constant_copy']} rawRows satisfied link_checked
  exact RowOrientationSoundness.checked_rows rho unoutlined rows rows_checked original
theorem inverse_equation {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : eval rho {inverse} * (point rho).x = 1 := by
  have actual := rows_satisfied rho satisfied
  have product := Compiler.checked_product_sound rho rows {inverse} {linear(x)}
    {product} {auxiliary} four actual (by decide) (by decide)
  have assertion := Compiler.checked_assertion_sound rho rows {product} [(0,1)]
    actual (by decide)
  rw [product] at assertion
  simpa only [point, eval, one, Int.cast_one, one_mul, add_zero] using assertion
theorem x_nonzero {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) : (point rho).x ≠ 0 := by
  intro zero
  have equation := inverse_equation rho one four satisfied
  rw [zero, mul_zero] at equation
  exact zero_ne_one equation
theorem represented_nonidentity {{F J : Type}} [Field F] [CharP F modulus] [AddCommGroup J]
    (d : F) (model : Group.StandardCurveModel J d) (represented : J)
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (meaning : model.coordinates represented = point rho)
    (satisfied : Satisfies rho rawRows) : represented ≠ 0 := by
  apply Group.represented_nonidentity d model represented
  rw [meaning]
  exact x_nonzero rho one four satisfied
'''
    for theorem in ('link_checked', 'rows_checked', 'rows_satisfied', 'inverse_equation', 'x_nonzero', 'represented_nonidentity'):
        source += '#print axioms ' + theorem + '\n'
    return name, _signature_audits(source + f'end ShielddSecurity.{name}\n')
