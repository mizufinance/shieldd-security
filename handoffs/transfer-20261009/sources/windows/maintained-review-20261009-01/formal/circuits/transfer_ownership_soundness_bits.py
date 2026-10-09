"""Expose validated ownership witness-bit handles to neutral local renderers."""
from . import transfer_ownership as owner
from . import transfer_relation as relation


def for_checked(checked):
    owner.match_formulas(checked)
    start = checked['metadata']['window_start']
    count = checked['metadata']['window_count']
    if count != len(checked['windows']) or len(checked['bits']) != 252:
        raise relation.RelationError('ownership soundness exact scalar/window cut')
    windows = []
    for offset in range(count):
        low = 2 * (125 - start - offset)
        handles = checked['bits'][low:low + 2]
        if len(handles) != 2 or any(handle not in checked['derived'] for handle in handles):
            raise relation.RelationError('ownership soundness validated source bits')
        # inspect_metadata already checks every captured window_bits pair equals
        # this exact reversed pair of the 252 validated source witness handles.
        windows.append(tuple(('source', handle) for handle in handles))
    return dict(checked, window_bits=windows)
