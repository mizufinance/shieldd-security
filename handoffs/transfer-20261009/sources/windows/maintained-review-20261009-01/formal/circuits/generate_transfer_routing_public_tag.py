"""Derive bounded public tag integers from actual Boolean/reconstruction rows."""
from . import transfer_routing_rows as routing, transfer_relation as relation
from .transfer_fixed_spend import canonical, combine
from .generate_transfer_routing_zero_rows import _lc, _row
from .generate_hash_round import _signature_audits


def generate(extraction):
    if extraction['schema'] != 'shieldd-transfer-routing-tag-rows-v1':
        raise relation.RelationError('captured routing tag derivative required')
    data = {item['row']: item for item in extraction['selected_rows']}
    raw = {index: tuple(canonical((column, int(value, 16)) for column, value in item[key])
                       for key in ('a', 'b')) for index, item in data.items()}
    link = extraction['plan']['constant_link']
    a, b = raw[link]
    if len(a) != 2 or b or a[0] != (0, 1) or a[1][1] != relation.MODULUS - 1:
        raise relation.RelationError('exact actual constant-copy assertion')
    copy = a[1][0]
    normalized = {index: tuple(canonical((0 if column == copy else column, value)
                        for column, value in terms) for terms in pair) for index, pair in raw.items()}
    table = routing._Rows(raw, normalized, copy)
    result = {}
    for slot in range(2):
        steps = sorted((step for step in extraction['plan']['tag_steps'] if step['slot'] == slot),
                       key=lambda step: step['index'])
        if [step['index'] for step in steps] != list(range(32)):
            raise relation.RelationError('exact ascending32 public bits')
        bits = [canonical(step['public']) for step in steps]
        value = canonical(extraction['plan']['flags'][5 + slot])
        if len(set(bits)) != 32:
            raise relation.RelationError('distinct public bit source operands')
        weighted = canonical((column, coefficient * pow(2, i, relation.MODULUS))
                             for i, bit in enumerate(bits) for column, coefficient in bit)
        reconstruct = table.exact(combine(weighted, value, -1), (), 'public tag reconstruction', True)
        booleans = [table.exact(bit, bit, 'public tag Boolean') for bit in bits]
        if booleans != [step['public_boolean_row'] for step in steps]:
            raise relation.RelationError('public Boolean physical source identity')
        indices = sorted(set([link, reconstruct, *booleans]))
        expected = [(bit, bit) for bit in bits] + [(combine(weighted, value, -1), ())]
        name = f'RuntimeRoutingPublicTag{slot}'
        source = f'''import ShielddSecurity.ScalarBits
import ShielddSecurity.RowOrientationSoundness
set_option maxHeartbeats 800000
namespace ShielddSecurity.{name}
def physicalIndices : List Nat := {indices}
def rawRows : List Row := [
''' + ',\n'.join(_row(data[index]['a'], data[index]['b']) for index in indices) + ']\n'
        source += 'def expectedRows : List Row := [\n' + ',\n'.join(_row(a, b) for a, b in expected) + ']\n'
        source += 'def bits : List Linear := [' + ','.join(_lc(bit) for bit in bits) + ']\n'
        source += f'''def value : Linear := {_lc(value)}
theorem bits_checked : ScalarBits.checkBits Scalar.modulus expectedRows bits = true := by decide
theorem reconstruction_checked : Compiler.checkRow Scalar.modulus expectedRows
    ⟨Compiler.subtract (ScalarBits.bitLinear bits) value, []⟩ = true := by decide
theorem canonical_integer {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    binary (ScalarBits.decodeBits rho bits) < 2 ^ 32 ∧
      (binary (ScalarBits.decodeBits rho bits) : F) = eval rho value := by
  have outlined := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied (by decide)
  have normalized := RowOrientationSoundness.checked_rows rho (Compiler.unoutlineRows {copy} rawRows)
    expectedRows (by decide) outlined
  have result := ScalarBits.checked_reconstruction rho expectedRows normalized bits value
    bits_checked reconstruction_checked
  have width : bits.length = 32 := by decide
  simpa only [width] using result
#print axioms bits_checked
#print axioms reconstruction_checked
#print axioms canonical_integer
end ShielddSecurity.{name}
'''
        result[name] = _signature_audits(source)
    return result
