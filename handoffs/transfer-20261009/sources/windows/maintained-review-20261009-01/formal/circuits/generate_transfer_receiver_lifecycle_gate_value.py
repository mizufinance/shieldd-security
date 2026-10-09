"""Project an accepted physical receiver gate onto its constrained bit column."""
import re
from . import transfer_relation as relation
from .generate_hash_round import linear, _signature_audits


def generate(gate_source, index, column, regulated):
    index = relation.natural(index, 131)
    if index not in (0, 1, 2, *range(67, 131)):
        raise relation.RelationError('actual receiver status/high-suffix gate required')
    column = relation.natural(column, 262144)
    regulated = relation.natural(regulated, 262144)
    if min(column, regulated) <= 2 or column == regulated:
        raise relation.RelationError('distinct physical receiver gate and bit columns required')
    namespace = f'RuntimeTransferReceiverLifecycleGate{index:03}'
    if f'namespace ShielddSecurity.{namespace}\n' not in gate_source:
        raise relation.RelationError('exact accepted receiver gate namespace required')
    expected = 1 if index == 0 else 0
    flag = linear(((regulated, 1),))
    terms = ((0, relation.MODULUS - 1), (column, 1)) if expected else ((column, 1),)
    bit = linear(terms)
    operands = []
    for name in ('left', 'right'):
        match = re.search(r'^def ' + name + r' : Linear := (\[[^\n]+\])$', gate_source, re.M)
        if match is None:
            raise relation.RelationError('closed physical gate operands required')
        operands.append(match.group(1))
    if sorted(operands) != sorted((flag, bit)):
        raise relation.RelationError('physical gate must constrain this exact regulated bit')
    name = f'TransferReceiverLifecycleGateValue{index:03}'
    source = f'''import ShielddSecurity.{namespace}
import ShielddSecurity.ReceiverLifecycleFieldStatus

set_option maxHeartbeats 200000

namespace ShielddSecurity.{name}

theorem value {{F : Type}} [Field F] [CharP F {namespace}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (enabled : rho {regulated} = 1) (satisfied : Satisfies rho {namespace}.rawRows) :
    rho {column} = {expected} := by
  have product := {namespace}.actual_gate rho four satisfied
  have forced : rho {column} - ({expected} : F) = 0 := by
    simpa [{namespace}.left,{namespace}.right,eval,one,enabled,mul_comm] using product
  exact sub_eq_zero.mp forced

theorem bit {{F : Type}} [Field F] [CharP F {namespace}.modulus]
    (rho : Nat → F) (one : rho 0 = 1) (four : (4 : F) ≠ 0)
    (enabled : rho {regulated} = 1) (satisfied : Satisfies rho {namespace}.rawRows)
    (b : Bool) (meaning : rho {column} = if b then 1 else 0) :
    b = {'true' if expected else 'false'} := by
  apply ReceiverLifecycleFieldStatus.boolean_injective (F := F)
  exact meaning.symm.trans (value rho one four enabled satisfied)

#print axioms value
#print axioms bit
end ShielddSecurity.{name}
'''
    return name, _signature_audits(source)
