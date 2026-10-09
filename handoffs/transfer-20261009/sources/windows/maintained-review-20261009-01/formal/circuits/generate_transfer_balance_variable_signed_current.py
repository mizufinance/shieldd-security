"""Replay signed-bit reuse against the current checked dependency closure."""
from . import generate_transfer_balance_variable_sequence as original
from . import transfer_relation as relation


def generate(accepted, signed):
    if len(accepted.get('programs', ())) != 65:
        raise relation.RelationError('signed reuse requires the genuine65 plan')
    modules = original.render_modules(accepted, original._kept(accepted, signed), 22738, signed)
    name = 'RuntimeBalanceVariableSequenceSigned'
    if set(modules) != {'RuntimeBalanceVariableSequence', name}:
        raise relation.RelationError('exact base and signed-reuse module split')
    return name, modules[name]
