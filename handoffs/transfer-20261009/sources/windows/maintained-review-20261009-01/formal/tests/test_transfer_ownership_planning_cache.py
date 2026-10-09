"""Typed source-planning cache checks; no actual capture/kernel credit."""
import unittest
from unittest.mock import patch

from circuits import transfer_ownership_planning_cache as cache
from circuits import generate_transfer_ownership_constructor_chunk as renderer
from circuits.transfer_relation import RelationError
from tests.test_transfer_ownership_constructor_chunk import fixture


class PlanningCacheTests(unittest.TestCase):
    def test_reuse_is_defensive_and_keys_keep_exact_types(self):
        checked, extracted = {'data': [1]}, {'rows': [[2]]}
        calls = []
        def plan(_checked, _extracted, offset, precompute, readonly):
            calls.append((offset, precompute, readonly))
            return {'writes': [offset], 'readonly': readonly}
        with patch.object(cache.completion, 'window_plan', side_effect=plan):
            with cache.planning_cache() as counts:
                first = cache.completion.window_plan(checked, extracted, 0, False, [(3, 1)])
                first['writes'].append(99)
                second = cache.completion.window_plan(checked, extracted, 0, False, [(3, 1)])
                self.assertEqual(second['writes'], [0])
                for offset, precompute, readonly in (
                        (False, False, [(3, 1)]), (0, 0, [(3, 1)]),
                        (0, True, [(3, 1)]), (0, False, ((3, 1),)),
                        (0, False, [(4, 1)])):
                    cache.completion.window_plan(checked, extracted, offset, precompute, readonly)
                self.assertEqual(counts['window'], {'hits': 1, 'misses': 6})
        self.assertEqual(len(calls), 6)

    def test_mutated_accepted_input_refuses_even_bool_int_alias(self):
        for family in ('checked', 'extracted'):
            checked, extracted = {'value': 1}, {'value': [1]}
            with patch.object(cache.completion, 'window_plan', return_value={'writes': [7]}):
                with cache.planning_cache():
                    cache.completion.window_plan(checked, extracted)
                    if family == 'checked':
                        checked['value'] = True
                    else:
                        extracted['value'][0] = True
                    with self.assertRaisesRegex(RelationError, 'mutation'):
                        cache.completion.window_plan(checked, extracted)

    def test_partition_reuses_window_and_restores_after_exception(self):
        checked, extracted = {'value': 1}, {'value': 2}
        def partition(c, e, offset, readonly):
            return cache.completion.window_plan(c, e, offset, False, readonly)
        with patch.object(cache.completion, 'window_plan', return_value={'writes': [7]}) as window, \
             patch.object(cache.joins, 'actual_window_partition', side_effect=partition) as original:
            with self.assertRaisesRegex(RuntimeError, 'sentinel'):
                with cache.planning_cache() as counts:
                    self.assertEqual(cache.joins.actual_window_partition(checked, extracted, 0), {'writes': [7]})
                    self.assertEqual(cache.joins.actual_window_partition(checked, extracted, 0), {'writes': [7]})
                    self.assertEqual(counts['partition'], {'hits': 1, 'misses': 1})
                    raise RuntimeError('sentinel')
            self.assertIs(cache.completion.window_plan, window)
            self.assertIs(cache.joins.actual_window_partition, original)
        self.assertFalse(cache._active)

    def test_nested_context_refuses_and_original_error_propagates(self):
        with patch.object(cache.completion, 'window_plan', side_effect=RelationError('strict planner')) as original:
            with cache.planning_cache():
                with self.assertRaisesRegex(RelationError, 'active context'):
                    with cache.planning_cache():
                        pass
                with self.assertRaisesRegex(RelationError, 'strict planner'):
                    cache.completion.window_plan({}, {})
            self.assertIs(cache.completion.window_plan, original)

    def test_mutation_during_unique_planning_refuses(self):
        for target in ('checked', 'readonly'):
            checked, extracted, readonly = {'data': [1]}, {}, [(3, 1)]
            def plan(c, _e, _offset, _precompute, roles):
                if target == 'checked':
                    c['data'].append(2)
                else:
                    roles.append((4, 1))
                return {'writes': [7]}
            with patch.object(cache.completion, 'window_plan', side_effect=plan):
                with cache.planning_cache():
                    with self.assertRaisesRegex(RelationError, 'mutation'):
                        cache.completion.window_plan(checked, extracted, 0, False, readonly)

    def test_small_generated_chunk_bytes_unchanged_and_repeat_hits(self):
        checked, extracted, plans = fixture(2)
        def plan(_checked, _extracted, offset, _precompute, _readonly):
            return plans[offset]
        with patch.object(cache.completion, 'window_plan', side_effect=plan), \
             patch.object(cache.joins, 'actual_window_partition', return_value={}):
            expected = renderer.generate(checked, extracted)
            with cache.planning_cache() as counts:
                self.assertEqual(renderer.generate(checked, extracted), expected)
                self.assertEqual(renderer.generate(checked, extracted), expected)
                self.assertEqual(counts['window'], {'hits': 2, 'misses': 2})
                self.assertEqual(counts['partition'], {'hits': 2, 'misses': 2})


if __name__ == '__main__':
    unittest.main()
