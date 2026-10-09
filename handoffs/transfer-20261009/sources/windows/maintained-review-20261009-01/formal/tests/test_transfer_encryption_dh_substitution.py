"""Actual formula/template matching on synthetic multi-term-base rows only."""
import copy
import unittest
from unittest.mock import patch
from circuits import transfer_encryption_dh_substitution as dh_substitution
from circuits import transfer_encryption_dh as dh, transfer_linear_substitution as substitution
from circuits.transfer_relation import MODULUS, RelationError


class DhTemplateSubstitutionTests(unittest.TestCase):
    def fixture(self):
        from tests.transfer_ownership_fixture import symbolic_window
        template, extracted = symbolic_window()
        target = copy.deepcopy(template)
        target['metadata'].update(schema='shieldd-transfer-encryption-dh-v1', role=0)
        target['qualified'] = True
        target['points'].pop('target')
        images = {3: ((503, 1), (504, 1)), 4: ((505, 1), (506, 1))}

        def substitute(terms):
            columns = {column: images.get(column, ((column, 1),)) for column, _ in terms}
            return substitution.linear(terms, columns)

        for key in ('derived', 'expressions'):
            target[key] = {handle: substitute(terms) for handle, terms in target[key].items() if handle not in ((1, 0), (1, 1))}
            target[key].update({(1, index): ((index + 3, 1),) for index in range(500, 504)})
            target[key][(2, 1)] = images[3]
            target[key][(2, 2)] = images[4]
        replace = lambda handle: (2, 1) if handle == (1, 0) else (2, 2) if handle == (1, 1) else handle
        target['nodes'] = {handle: (multiply, replace(left), replace(right)) for handle, (multiply, left, right) in target['nodes'].items()}
        target['nodes'].update({(2, 1): (False, (1, 500), (1, 501)), (2, 2): (False, (1, 502), (1, 503))})
        target['points']['base'] = (('source', (2, 1)), ('source', (2, 2)))
        target['bindings'] = dict(flagged=('source', target['bits'][248]),
                                  detection_key=target['points']['base'], payload_key=target['points']['base'])
        rows = []
        for original in extracted['selected_rows']:
            row = dict(row=original['row'])
            for side in ('a', 'b'):
                terms = tuple((column, int(value, 16)) for column, value in original[side])
                row[side] = [[column, f'{factor:064x}'] for column, factor in substitute(terms)]
            rows.append(row)
        for index in (248, 249):
            terms = [[target['bits'][index][1] + 3, f'{1:064x}']]
            rows.append(dict(row=max(row['row'] for row in rows) + 1, a=terms, b=terms))
        full_rows = max(template['metadata']['full_rows'], max(row['row'] for row in rows) + 1)
        target['metadata']['full_rows'] = template['metadata']['full_rows'] = full_rows
        extracted['identity']['stored_rows'] = full_rows

        def replay(stream, expected_relation, row_observer):
            selected = {row['row']: row for row in rows}
            for index in range(full_rows):
                row_observer(selected.get(index, dict(row=index, a=[], b=[])))
            return dict(relation_digest='a' * 64, domain_size=16384, stored_rows=full_rows)

        with patch.object(dh.relation, 'inspect', side_effect=replay):
            actual = dh.extract_rows(target, None, 'a' * 64)
        # Match the original selected Boolean rows as well. They do not change
        # under this synthetic base-only substitution.
        for index, row in zip((248, 249), rows[-2:]):
            extracted['selected_rows'].append(copy.deepcopy(row))
            extracted['templates'].append(dict(roles=['bit.' + str(index)], row=row['row']))
        return template, extracted, target, actual

    def test_real_cone_and_compiler_matching_accepts_complete_lc_images(self):
        template, extracted, target, actual = self.fixture()
        selected = dh_substitution.window_substitution(template, extracted, target, actual, include_precompute=True)
        columns = dict(selected['columns'])
        self.assertEqual(columns[3], ((503, 1), (504, 1)))
        self.assertEqual(columns[4], ((505, 1), (506, 1)))
        self.assertEqual(len(selected['row_targets']), len(selected['source_rows']))
        self.assertIn('transport OPEN', selected['scope'])

    def test_wrong_formula_and_missing_product_row_are_refused(self):
        for edit in ('formula', 'row', 'qualification'):
            template, extracted, target, actual = self.fixture()
            if edit == 'formula':
                handle = next(handle for handle, node in target['nodes'].items() if handle[1] > 2 and node[0])
                multiply, left, right = target['nodes'][handle]
                target['nodes'][handle] = (False, left, right)
            elif edit == 'row':
                omitted = actual['products'][0]['rows'][0]
                actual['selected_rows'] = [row for row in actual['selected_rows'] if row['row'] != omitted]
            else:
                target['qualified'] = False
            with self.subTest(edit=edit), self.assertRaises(RelationError):
                dh_substitution.window_substitution(template, extracted, target, actual, include_precompute=True)

    def test_outlined_constant_roles_require_actual_copy_assertion(self):
        template, extracted, target, actual = self.fixture()
        copy_column = target['metadata']['constant_copy']
        for row in actual['selected_rows']:
            # Only compiler arithmetic rows outline zero; preserve the one
            # physical equality that connects the copy to column zero.
            is_link = any(column == copy_column for column, _ in row['a']) and not row['b']
            if not is_link:
                for side in ('a', 'b'):
                    row[side] = [[copy_column if column == 0 else column, factor]
                                 for column, factor in row[side]]
        checked = dh_substitution.window_substitution(template, extracted, target, actual, include_precompute=True)
        self.assertTrue(checked['unoutlined'])
        self.assertEqual(dict(checked['columns'])[template['metadata']['constant_copy']], ((0, 1),))
        self.assertEqual(checked['actual_copy'], copy_column)
        # The raw assertion remains necessary; normalization cannot invent it.
        changed = copy.deepcopy(actual)
        changed['selected_rows'] = [row for row in changed['selected_rows']
                                   if not (any(column == copy_column for column, _ in row['a']) and not row['b'])]
        with self.assertRaises(RelationError):
            dh_substitution.window_substitution(template, extracted, target, changed, include_precompute=True)

    def test_chunk_bit_role_and_original_boolean_rows(self):
        template, extracted, target, actual = self.fixture()
        selected = dh_substitution.chunk_substitution(template, extracted, target, actual)
        self.assertEqual(len(selected['windows']), 1)
        self.assertEqual(dict(selected['columns'])[3], ((503, 1), (504, 1)))
        for edit in ('role', 'row', 'interval'):
            changed = copy.deepcopy(target)
            changed_rows = copy.deepcopy(actual)
            if edit == 'role': changed['bits'][248], changed['bits'][249] = changed['bits'][249], changed['bits'][248]
            elif edit == 'row':
                omitted = next(item['row'] for item in actual['templates'] if 'bit.248' in item['roles'])
                changed_rows['selected_rows'] = [row for row in changed_rows['selected_rows'] if row['row'] != omitted]
            else: changed['metadata']['window_start'] = 2
            with self.subTest(edit=edit), self.assertRaises(RelationError):
                dh_substitution.chunk_substitution(template, extracted, changed, changed_rows)

    def test_common_assignment_merge_retains_multi_term_images(self):
        template, extracted, target, actual = self.fixture()
        checked = dh_substitution.chunk_substitution(template, extracted, target, actual)
        # Repeating this synthetic local packet tests assignment assembly only;
        # it is not full126 metadata and cannot pass full_substitution's ingress.
        merged = dh_substitution.merge_substitutions([copy.deepcopy(checked) for _ in range(8)])
        self.assertEqual(dict(merged['columns'])[3], ((503, 1), (504, 1)))
        self.assertEqual(merged['source_rows'], checked['source_rows'])
        self.assertEqual(merged['row_targets'], checked['row_targets'])

    def test_common_assignment_merge_refuses_conflicts_and_missing_rows(self):
        template, extracted, target, actual = self.fixture()
        checked = dh_substitution.chunk_substitution(template, extracted, target, actual)
        for edit in ('image', 'physical', 'target', 'missing', 'coverage', 'duplicate', 'constant', 'pages'):
            pages = [copy.deepcopy(checked) for _ in range(8)]
            changed = pages[-1]
            original, row = changed['row_targets'][0]
            if edit == 'image':
                changed['columns'] = [(column, ((900, 1),) if column == 3 else terms)
                                      for column, terms in changed['columns']]
            elif edit == 'physical': changed['actual_rows'][row] = ((), ())
            elif edit == 'target': changed['row_targets'][0] = (original, row + 100000)
            elif edit == 'missing':
                for page in pages: page['actual_rows'].pop(row)
            elif edit == 'coverage':
                for page in pages: page['row_targets'] = page['row_targets'][1:]
            elif edit == 'duplicate': changed['columns'].append(changed['columns'][0])
            elif edit == 'constant':
                for page in pages: page['columns'] = [(column, ((0, 2),) if column == 0 else terms)
                                                      for column, terms in page['columns']]
            else: pages.pop()
            with self.subTest(edit=edit), self.assertRaises(RelationError):
                dh_substitution.merge_substitutions(pages)
