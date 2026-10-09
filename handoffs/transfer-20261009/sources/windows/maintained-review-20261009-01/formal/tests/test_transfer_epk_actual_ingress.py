import unittest
from unittest.mock import patch
from integration import transfer_epk_actual_ingress as ingress
from circuits.transfer_relation import RelationError


class ActualEpkIngressTests(unittest.TestCase):
    def test_all_six_eight_page_selectors_and_last_page(self):
        for scope in range(6):
            for page in range(8):
                ingress._selector('page', scope, page)
            ingress._selector('canonical', scope, None)
            ingress._selector('whole', scope, None)
        ingress._selector('six', None, None)

    def test_refuses_boolean_and_dropped_scope_selectors(self):
        for args in [('page', True, 0), ('page', 0, True), ('page', 0, 8),
                     ('whole', 6, None), ('whole', 0, 0), ('six', 0, None),
                     ('canonical', None, None), ('unknown', None, None)]:
            with self.assertRaises(RelationError):
                ingress._selector(*args)

    def test_does_not_render_without_actual_parent_identity(self):
        # A replay-count assertion alone is insufficient; rejection precedes
        # parser/renderers and cannot create a forged runtime certificate.
        with self.assertRaisesRegex(RelationError, 'retained actual replay identity'):
            list(ingress.generate(b'parent', [b'page'], {}, {}, {'ordinary_replays': 1}, 'page', 0, 0))

    def test_last_page_reaches_all_fourteen_windows_with_whole_fixed_selection(self):
        parent, pages = b'parent', [b'page']
        digest, ids = ingress._ids(parent, pages)
        fixed = object()
        extracted = dict(parent_sha256=digest, raw_page_sha256=ids, ordinary_replays=1, fixed=fixed)
        chunks = [None] * 7 + [dict(metadata=dict(window_start=112, window_count=14))]
        calls = []
        def renderer(*args):
            self.assertIs(args[4], fixed)
            calls.append(args[5:])
            return 'fixture source'
        with patch.object(ingress.program, 'plan', return_value=dict(chunks=chunks)), \
             patch.object(ingress.epk, 'inspect_all_pages', return_value={}), \
             patch.object(ingress.batch, 'page_selection', return_value={}), \
             patch.object(ingress.render, 'generate_window', renderer), \
             patch.object(ingress.render, 'generate_window_completion', renderer), \
             patch.object(ingress.render, 'generate_window_complete', renderer):
            emitted = list(ingress.generate(parent, pages, {}, {}, extracted, 'page', 5, 7))
        self.assertEqual(len(emitted), 42)
        self.assertEqual(len({name for name, _ in emitted}), 42)
        self.assertEqual({call[2] for call in calls}, set(range(14)))
        self.assertTrue(any(name == 'RuntimeTransferEpk5FixedWindow125CurveCompletion' for name, _ in emitted))

