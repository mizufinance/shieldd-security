"""Synthetic renderer controls; no imported Lean or runtime qualification."""
import unittest
from circuits import generate_transfer_encryption_dh_transport as renderer
from circuits.transfer_relation import RelationError


class DhTransportRendererTests(unittest.TestCase):
    def source(self, start=0):
        count = min(16, 126 - start)
        names = [f'rows{index}' for index in range(count)] + ['bitRows']
        return (f'namespace ShielddSecurity.RuntimeRnkTrace{start:03d}\n' +
                ''.join(f'def {name} : List Row := [⟨[(3, (1 : Int))], [(4, (-1 : Int))]⟩]\n' for name in names) +
                'def blocks : List (List Row) := [' + ', '.join(names) + ']\n' +
                'def rawRows : List Row := blocks.flatten\n' +
                'theorem fixture_only : True := True.intro\n')

    def test_literal_blocks_have_exact_window_and_boolean_coverage(self):
        for start in range(0, 126, 16):
            blocks = renderer.template_blocks(self.source(start), start)
            self.assertEqual(len(blocks), min(16, 126 - start) + 1)
            self.assertEqual(blocks[-1], ('bitRows', [(((3, 1),), ((4, -1),))]))

    def test_source_namespace_coverage_and_nonliteral_rows_are_refused(self):
        for source in (self.source().replace('RuntimeRnkTrace000', 'RuntimeOwnershipTrace000'),
                       self.source().replace('rows8, ', ''),
                       self.source().replace('(4, (-1 : Int))', '(4, arbitraryCoefficient)'),
                       self.source().replace('blocks.flatten', '[]'),
                       self.source().replace('rows0 : List Row := [', 'rows0 : List Row := missing ++ [')):
            with self.subTest(source=source[:60]), self.assertRaises(RelationError):
                renderer.template_blocks(source, 0)

    def test_complete_lc_map_data_pages_are_bounded_and_constant_bound(self):
        entries = [(0, ((0, 1),))] + [(index, ((index + 500, 1),)) for index in range(1, 130)]
        name, source = renderer.map_source(4, entries)
        self.assertEqual(name, 'RuntimeTransferEncryptionDh4Map')
        self.assertIn('def part1', source)
        self.assertIn('def part0 : MapTree', source)
        self.assertEqual(source.count('if column = key then value else []'), 1)
        self.assertEqual(source.count('if column < pivot then lookup left column else lookup right column'), 1)
        self.assertIn('MapTree.leaf 129 [(629, (1 : Int))]', source)
        _, sparse = renderer.map_source(0, [(0, ((0, 1),)), (17, ()),
                                               (30, ((50, 2), (51, 3)))])
        self.assertIn('MapTree.leaf 17 []', sparse)
        self.assertIn('MapTree.leaf 30 [(50, (2 : Int)), (51, (3 : Int))]', sparse)
        self.assertIn('lookup part0 column', sparse)
        self.assertIn('#check @columns_zero', source)
        self.assertNotIn('native_decide', source)
        for changed in (entries[::-1], entries + [entries[-1]], [(0, ((0, 2),))]):
            with self.assertRaises(RelationError): renderer.map_source(4, changed)

    def test_row_checks_bind_multi_term_images_and_original_physical_rows(self):
        columns = {0: ((0, 1),), 3: ((503, 1), (504, 1)), 4: ((505, 1),)}
        template = [(((3, 1),), ((4, 1),))]
        actual = {70: (((503, 1), (504, 1)), ((505, 1),))}
        _, source = renderer.row_source(0, 0, 0, 'rows0', template, columns, actual)
        self.assertIn('originalRows : List Nat := [70]', source)
        self.assertIn('RuntimeRnkTrace000.rows0.map', source)
        self.assertIn('RowLinearSubstitutionSoundness.checked_rows', source)
        self.assertIn('#check @source_satisfied', source)
        with self.assertRaises(RelationError):
            renderer.row_source(0, 0, 0, 'rows0', template, columns,
                                {70: (actual[70][0], ((505, 2),))})

    def test_reversed_square_is_accepted_but_zero_rows_are_not_invented(self):
        columns = {0: ((0, 1),), 3: ((503, 1),), 4: ((504, 1),)}
        template = [(((3, 1),), ((4, 1),))]
        _, source = renderer.row_source(0, 0, 0, 'rows0', template, columns,
                                        {90: (((503, -1),), ((504, 1),))})
        self.assertIn('originalRows : List Nat := [90]', source)
        with self.assertRaises(RelationError):
            renderer.row_source(0, 0, 0, 'rows0', [((), ())], columns,
                                {90: (((503, 1),), ((504, 1),))})

    def test_copy_normalization_keeps_raw_rows_and_proves_the_link(self):
        columns = {0: ((0, 1),), 3: ((503, 1), (0, 2)), 4: ((504, 1),)}
        template = [(((3, 1),), ((4, 1),))]
        actual = {90: (((503, 1), (902, 2)), ((504, 1),)),
                  91: (((0, 1), (902, -1)), ())}
        _, source = renderer.row_source(0, 0, 0, 'rows0', template, columns, actual, actual_copy=902)
        self.assertIn('originalRows : List Nat := [90, 91]', source)
        self.assertIn('Compiler.unoutlineRows 902 rawRows', source)
        self.assertIn('Compiler.unoutline_rows_sound rho 902 rawRows satisfied link', source)
        self.assertIn('(902, (2 : Int))', source)
        statement = source.split('theorem source_satisfied', 1)[1].split(' := by', 1)[0]
        self.assertNotIn('linked', statement)
        for rows in ({90: actual[90]}, {**actual, 91: (((0, 1), (902, -2)), ())}):
            with self.assertRaises(RelationError):
                renderer.row_source(0, 0, 0, 'rows0', template, columns, rows, actual_copy=902)

    def test_complete_source_signature_derives_endpoint_from_actual_rows(self):
        blocks = {start: [name for name, _ in renderer.template_blocks(self.source(start), start)]
                  for start in range(0, 126, 16)}
        synthetic = dict(qualified=True, windows=126, role=0, loop_roles={
            'base': dict(source=[((1520, 1),), ((1521, 1),)], actual=[((700, 1),), ((701, 1),)]),
            'output': dict(source=[((3763, 1),), ((3764, 1),)], actual=[((800, 1),), ((801, 1),)]),
            'bits': dict(source=[((2000 + bit, 1),) for bit in range(252)],
                         actual=[((1000 + bit, 1),) for bit in range(252)])})
        _, source = renderer.loop_source(synthetic, blocks)
        statement = source.split('theorem actual_multiplication ', 1)[1].split(' := by', 1)[0]
        self.assertIn('Satisfies rho rawRows', statement)
        self.assertIn('baseRole : base rho = model.coordinates inputBase', statement)
        self.assertIn('output rho = model.coordinates', statement)
        self.assertNotIn('(outputRole', statement)
        self.assertNotIn('(hashRole', statement)
        self.assertIn('RowLinearSubstitutionSoundness.decode_bits', source)
        self.assertIn('#check @actual_multiplication', source)
        self.assertEqual(source.count('#print axioms '), source.count('#check @'))
        # Synthetic rendering does not run these finite checks or establish a
        # real qualified capture, row satisfaction or any group conclusion.
        with self.assertRaises(RelationError): renderer.loop_source(synthetic, {0: blocks[0]})
        with self.assertRaises(RelationError): renderer.loop_source({**synthetic, 'qualified': False}, blocks)
        with self.assertRaises(RelationError): renderer.loop_source(synthetic, {**blocks, 0: blocks[0][:-1]})
        with self.assertRaises(RelationError): renderer.loop_source(synthetic, {**blocks, 0: [*blocks[0][:-1], 'arbitraryRows']})
        with self.assertRaises(RelationError): renderer.chunk_source(0, 0, [*blocks[0][:-1], 'arbitraryRows'])
