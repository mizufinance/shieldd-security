"""Typed folded-path refusal tests; no observed runtime/kernel credit."""
import copy
import unittest
from unittest.mock import patch
from circuits import generate_transfer_ownership_folded_window_completion as generator
from circuits.transfer_relation import RelationError


def fixture():
    identity = (('native', 0), ('native', 1))
    checked = dict(metadata=dict(window_start=0, constant_copy=100), windows=[(identity, identity, identity)])
    plan = dict(point_groups=[dict(stage_start=0, stage_end=0), dict(stage_start=0, stage_end=0),
                              dict(material_end=1, stage_end=3)],
                stages=[dict(kind='product'), dict(kind='linear'), dict(kind='linear')])
    name = 'RuntimeOwnershipWindow000Completion'
    source = f'namespace ShielddSecurity.{name}\nend ShielddSecurity.{name}\n'
    return checked, {}, plan, (name, source)


class FoldedWindowCompletionTests(unittest.TestCase):
    def render(self, values):
        checked, extracted, plan, local = values
        with patch.object(generator.completion, 'window_plan', return_value=plan), \
                patch.object(generator.local, 'generate', return_value=local):
            return generator.generate(checked, extracted)

    def test_constructs_original_rows_without_division_legality_premise(self):
        name, source = self.render(fixture())
        self.assertEqual(name, 'RuntimeOwnershipWindow000FoldedCompletion')
        statement = source.split('theorem constructs', 1)[1].split(' := by', 1)[0]
        self.assertIn('Satisfies (completeAssignment base) rawRows', statement)
        self.assertNotIn('legal', statement)
        self.assertNotIn('Satisfies base', statement)
        self.assertIn('CompilerCompletion.Step.Legal', source)

    def test_only_exact_initial_folded_path(self):
        for mutation in ('later', 'nonidentity', 'doublewrite', 'quotient', 'extra'):
            values = copy.deepcopy(fixture())
            if mutation == 'later': values[0]['metadata']['window_start'] = 1
            elif mutation == 'nonidentity': values[0]['windows'][0] = [(("native", 1), ("native", 1))] * 3
            elif mutation == 'doublewrite': values[2]['point_groups'][0]['stage_end'] = 1
            elif mutation == 'quotient': values[2]['stages'][1]['kind'] = 'quotient'
            else: values[2]['point_groups'].append(dict(stage_start=0, stage_end=0))
            with self.subTest(mutation=mutation), self.assertRaises(RelationError):
                self.render(values)


if __name__ == '__main__':
    unittest.main()
