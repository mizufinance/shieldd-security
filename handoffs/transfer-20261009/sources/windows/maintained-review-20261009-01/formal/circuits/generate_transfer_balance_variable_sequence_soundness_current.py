"""Finish the reduced adjacency certificate without changing sequence claims."""
from . import generate_transfer_balance_variable_sequence_soundness as original
from . import transfer_relation as relation


def generate(accepted):
    name, source = original.generate(accepted)
    old = 'GroupFixedCircuitCompletion.Aligned,\n'
    if source.count(old) != 1:
        raise relation.RelationError('exact sequence adjacency simplification boundary')
    return name, source.replace(old, 'GroupFixedCircuitCompletion.Aligned,true_and,\n')
