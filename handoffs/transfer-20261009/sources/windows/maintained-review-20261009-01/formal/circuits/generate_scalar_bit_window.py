"""Original remainder Boolean rows in bounded consecutive windows.

This is a source generator, not a certificate. It adds the missing Boolean
premises for the existing actual comparator windows. Whole-list reconstruction,
terminal products, source projection and legal-input completion are separate.
"""
from generate_hash_round import linear
from hash_rows import canonical
from poseidon_graph import P
from scalar_rows import select


def generate(export, parameter_root, export_hash, start, count):
    if type(export_hash) is not str or len(export_hash) != 64 or any(c not in '0123456789abcdef' for c in export_hash):
        raise ValueError('exact lowercase SHA256 export identity required')
    if type(start) is not int or type(count) is not int or not 0 <= start < 252 or not 1 <= count <= 32 or start + count > 252:
        raise ValueError('Boolean window must contain 1..32 original consecutive remainder bits')
    selected = select(export, parameter_root, 'remainder')
    complete = selected['bits']['remainder']
    if len(complete) != 252 or len(set(complete)) != 252:
        raise ValueError('changed or aliased original remainder bit list')
    chosen = complete[start:start + count]
    table = {}
    for index, pair in sorted(selected['rows'].items()):
        # Use the same exact copy substitution as the reviewed scalar selector.
        normalized = tuple(canonical((0 if column == selected['outline'] else column, coefficient)
                                     for column, coefficient in terms) for terms in pair)
        table.setdefault(normalized, index)
    original_indices = []
    for bit in chosen:
        if len(bit) != 1 or bit[0][0] < 3 or bit[0][1] != 1 or bit[0][0] == selected['outline']:
            raise ValueError('unsupported original Boolean witness projection')
        if (bit, bit) not in table:
            raise ValueError('missing original Boolean row')
        original = table[(bit, bit)]
        # These witness diagonals require no constant-copy premise. Reject a
        # future compiler representation needing any extra row transformation.
        if selected['rows'][original] != (bit, bit):
            raise ValueError('Boolean row is not the exact original witness diagonal')
        original_indices.append(original)
    if len(set(original_indices)) != count:
        raise ValueError('aliased original Boolean row indices')
    module = f'RuntimeScalarRemainderBitsWindow{start}_{count}'
    rows = ',\n'.join('  ⟨' + linear(bit) + ', ' + linear(bit) + '⟩' for bit in chosen)
    bits = ',\n'.join('  ' + linear(bit) for bit in chosen)
    return f'''import ShielddSecurity.ScalarBits
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{module}
-- Exact exported source/rows SHA256: {export_hash}
-- Relation digest (identity only): {export['relation_digest']}
-- Original row indices, in original bit order: {original_indices}
-- Original remainder bits [{start}, {start + count}); no wide data checker.
def modulus : Nat := {P}
def rawRows : List Row := [
{rows}
]
def bits : List Linear := [
{bits}
]
theorem certificate : ScalarBits.checkBits modulus rawRows bits = true := by decide

theorem actual_bits_value {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho (ScalarBits.bitLinear bits) = (binary (ScalarBits.decodeBits rho bits) : F) := by
  exact ScalarBits.decoded_bits_value rho rawRows satisfied bits certificate

#print axioms certificate
#print axioms actual_bits_value
end ShielddSecurity.{module}
'''
