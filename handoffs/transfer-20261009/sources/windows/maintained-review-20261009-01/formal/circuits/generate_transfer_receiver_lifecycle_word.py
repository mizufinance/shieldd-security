"""Identify every receiver lifecycle bit from the accepted physical range rows."""
import ast
import re
from . import transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(range_source):
    namespace = 'RuntimeTransferReceiverLifecycleRange'
    if not isinstance(range_source, str) or f'namespace ShielddSecurity.{namespace}\n' not in range_source:
        raise relation.RelationError('exact accepted receiver lifecycle range module required')
    columns_match = re.search(r'^def bits : List Nat := (\[[0-9, ]+\])$', range_source, re.M)
    value_match = re.search(r'theorem actual_range\b.*?∃ n : Nat,\s*n < 2\^131 ∧ \(n : F\) = rho (\d+) := by', range_source, re.S)
    if columns_match is None or value_match is None:
        raise relation.RelationError('closed accepted receiver bit-word/value declarations required')
    columns = ast.literal_eval(columns_match.group(1))
    value = int(value_match.group(1))
    if (len(columns) != 131 or any(type(c) is not int for c in columns) or
            columns != list(range(columns[0], columns[0] + 131)) or value in columns or
            columns[0] <= 2 or value <= 2):
        raise relation.RelationError('actual disjoint contiguous 131-bit receiver layout required')
    if re.search(r'^theorem word\b', range_source, re.M) is None:
        raise relation.RelationError('bounded same-word range theorem required')
    name = 'TransferReceiverLifecycleWord'
    source = f'''import ShielddSecurity.ReceiverLifecycleWordSoundness
import ShielddSecurity.{namespace}

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.{name}

theorem word {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho {namespace}.rawRows) :
    ∃ n : Nat,n < 2^131 ∧ (n : F) = rho {value} ∧
      {namespace}.bits.map rho = (encodeBits 131 n).map (fun bit => if bit then (1 : F) else 0) := by
  exact {namespace}.word rho satisfied

#print axioms word
end ShielddSecurity.{name}
'''
    return name, _signature_audits(source)
