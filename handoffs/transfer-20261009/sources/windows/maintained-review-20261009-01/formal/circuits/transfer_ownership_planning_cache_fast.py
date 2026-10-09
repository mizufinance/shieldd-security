"""Job-local exact structural caching with C-level repeat fingerprints.

The original recursive snapshot validates the allowed input types once.
Marshal signatures retain their types, values, ordering and reference structure;
repeat observations still reject mutations. No signature is proof evidence.
"""
from contextlib import contextmanager
from copy import deepcopy
import marshal

from . import transfer_ownership_planning_cache as original
from . import transfer_ownership_completion as completion
from . import transfer_ownership_constructor_join as joins
from .transfer_relation import RelationError


@contextmanager
def planning_cache():
    if original._active:
        raise RelationError('ownership planning cache requires one active context')
    original_window = completion.window_plan
    original_partition = joins.actual_window_partition
    tracked = {}
    cached = {}
    counts = {'window': {'hits': 0, 'misses': 0},
              'partition': {'hits': 0, 'misses': 0}}

    def observe(value):
        identity = id(value)
        if identity not in tracked:
            original._snapshot(value)
        try:
            signature = marshal.dumps(value, 4)
        except (TypeError, ValueError) as error:
            raise RelationError('ownership planning cache unsupported typed input') from error
        if identity in tracked:
            retained, expected = tracked[identity]
            if retained is not value or signature != expected:
                raise RelationError('ownership planning cache accepted input mutation')
        else:
            tracked[identity] = value, signature
        return identity

    def invoke(family, function, checked, extracted, offset, precompute, readonly):
        checked_id, extracted_id = observe(checked), observe(extracted)
        key = (family, checked_id, extracted_id, original._snapshot(offset),
               original._snapshot(precompute), original._snapshot(readonly))
        if key in cached:
            counts[family]['hits'] += 1
            return deepcopy(cached[key])
        counts[family]['misses'] += 1
        result = (function(checked, extracted, offset, precompute, readonly)
                  if family == 'window' else function(checked, extracted, offset, readonly))
        observe(checked)
        observe(extracted)
        if original._snapshot(readonly) != key[-1]:
            raise RelationError('ownership planning cache readonly mutation')
        cached[key] = deepcopy(result)
        return deepcopy(result)

    def window(checked, extracted, window_offset=0, include_precompute=True, readonly_lcs=()):
        return invoke('window', original_window, checked, extracted,
                      window_offset, include_precompute, readonly_lcs)

    def partition(checked, extracted, window_offset, readonly_lcs=()):
        return invoke('partition', original_partition, checked, extracted,
                      window_offset, None, readonly_lcs)

    original._active = True
    completion.window_plan = window
    joins.actual_window_partition = partition
    try:
        yield counts
    finally:
        completion.window_plan = original_window
        joins.actual_window_partition = original_partition
        original._active = False
