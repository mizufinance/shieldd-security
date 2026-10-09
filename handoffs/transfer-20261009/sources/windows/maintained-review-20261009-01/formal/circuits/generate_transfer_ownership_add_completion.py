"""Exact nonfolded precomputed3base addition after owned materializations.

Both incoming curve facts remain independent local input contracts. The native
seed/precomputed2base constructor must derive them before whole composition.
"""
from .generate_transfer_ownership_double_completion import _generate, completion


def generate(checked, extracted, readonly_lcs=()):
    return _generate(checked, extracted, readonly_lcs, 1)


def generate_window_addition(checked, extracted, window_offset, readonly_lcs=()):
    """Actual nonfolded addition after constructing its selector materializations.

    Right input curve validity refers to the constructed selector, not an
    arbitrary initial value of its product columns. The selector/Boolean/curve
    join must derive that fact before the whole variable-window constructor.
    """
    if type(window_offset) is not int or not 0 <= window_offset < len(checked['windows']):
        raise completion.relation.RelationError('ownership typed bounded window addition selection')
    return _generate(checked, extracted, readonly_lcs, 4+3*window_offset, window_offset, False)
