import unittest
from integration.transfer_balance_final_rows_diagnostic import Slice


class DiagnosticSliceTests(unittest.TestCase):
    def test_direct_source_never_propagates_into_unrelated_scalar_chain(self):
        collector = Slice()
        row = lambda index, a, b: dict(row=index, a=[[c, '1'] for c in a], b=[[c, '1'] for c in b])
        collector.observe(row(0, [21711], [30000]))
        for index in range(1, 3000):
            collector.observe(row(index, [29999+index], [30000+index]))
        self.assertEqual(list(collector.rows), [0])

    def test_exact_final_output_neighbours_are_bounded_both_sides(self):
        collector = Slice()
        for index in range(230):
            collector.observe(dict(row=index, a=[[195230 if index == 100 else index+50000, '1']], b=[]))
        self.assertEqual(sorted(collector.rows), list(range(36, 165)))
        self.assertEqual(collector.reasons[100], {'direct-seed', 'final-output-neighbour'})
