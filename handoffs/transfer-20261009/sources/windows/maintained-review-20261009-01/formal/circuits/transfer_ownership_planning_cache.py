"""Job-local reuse of strict ownership plans for the same immutable inputs.

Every unique plan is computed by the existing strict planner. Structural
snapshots refuse mutated accepted inputs, and returned copies cannot alter a
later reuse. This changes neither source acceptance nor generated proof text.
"""
from contextlib import contextmanager
from copy import deepcopy

from . import transfer_ownership_completion as completion
from . import transfer_ownership_constructor_join as joins
from .transfer_relation import RelationError

_active = False


def _snapshot(value, ancestors=()):
    kind = type(value)
    if kind in (str, int, bool, bytes, type(None)):
        return kind, value
    if kind not in (dict, list, tuple, set, frozenset):
        raise RelationError('ownership planning cache unsupported typed input')
    identity = id(value)
    if identity in ancestors:
        raise RelationError('ownership planning cache cyclic input')
    nested = ancestors + (identity,)
    if kind is dict:
        return kind, tuple((_snapshot(key, nested), _snapshot(item, nested))
                           for key, item in value.items())
    items = (_snapshot(item, nested) for item in value)
    return kind, frozenset(items) if kind in (set, frozenset) else tuple(items)


@contextmanager
def planning_cache():
    """Cache strict window/partition calls within one sequential source job.

    A nested context is refused because the module functions are temporarily
    wrapped. The originals are restored on success and every exception.
    """
    global _active
    if _active:
        raise RelationError('ownership planning cache requires one active context')
    original_window = completion.window_plan
    original_partition = joins.actual_window_partition
    tracked = {}
    cached = {}
    counts = {'window': {'hits': 0, 'misses': 0},
              'partition': {'hits': 0, 'misses': 0}}

    def observe(value):
        identity = id(value)
        snapshot = _snapshot(value)
        if identity in tracked:
            original, expected = tracked[identity]
            if original is not value or snapshot != expected:
                raise RelationError('ownership planning cache accepted input mutation')
        else:
            # A strong reference prevents object-id reuse during the context.
            tracked[identity] = value, snapshot
        return identity

    def invoke(family, function, checked, extracted, offset, precompute, readonly):
        checked_id, extracted_id = observe(checked), observe(extracted)
        key = (family, checked_id, extracted_id, _snapshot(offset),
               _snapshot(precompute), _snapshot(readonly))
        if key in cached:
            counts[family]['hits'] += 1
            return deepcopy(cached[key])
        counts[family]['misses'] += 1
        result = (function(checked, extracted, offset, precompute, readonly)
                  if family == 'window' else function(checked, extracted, offset, readonly))
        observe(checked)
        observe(extracted)
        if _snapshot(readonly) != key[-1]:
            raise RelationError('ownership planning cache readonly mutation')
        cached[key] = deepcopy(result)
        return deepcopy(result)

    def window(checked, extracted, window_offset=0, include_precompute=True, readonly_lcs=()):
        return invoke('window', original_window, checked, extracted,
                      window_offset, include_precompute, readonly_lcs)

    def partition(checked, extracted, window_offset, readonly_lcs=()):
        return invoke('partition', original_partition, checked, extracted,
                      window_offset, None, readonly_lcs)

    _active = True
    completion.window_plan = window
    joins.actual_window_partition = partition
    try:
        yield counts
    finally:
        completion.window_plan = original_window
        joins.actual_window_partition = original_partition
        _active = False
