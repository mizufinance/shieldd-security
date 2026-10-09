"""Required source/refusal tests; no actual five-page capture is available."""
import copy,importlib.util,unittest
from pathlib import Path
from circuits import generate_transfer_balance_variable_sequence as sequence
from circuits import generate_transfer_balance_variable_completion as local
from circuits import transfer_relation as relation
from tests.test_transfer_balance_variable_completion import accepted_fixture
from tests.test_transfer_signed_balance_completion import SignedBalanceCompletionTests
from circuits import transfer_signed_balance_completion as signed


class BalanceVariableSequenceTests(unittest.TestCase):
    def test_reused_bits_keep_all_owned_signed_rows_and_wrong_magnitude_fails(self):
        fixture=SignedBalanceCompletionTests();fixture.setUp();recipe=fixture.recipe
        for amounts in ([0,0,0,0],[8,1,3,2],[3,2,8,1],[(1<<128)-1,(1<<128)-1,0,0]):
            base={0:1,recipe['copy']:1,**dict(zip(recipe['amounts'],amounts))}
            constructed=signed.construct(recipe,base,amounts)
            assignment=constructed['assignment'];magnitude=constructed['magnitude']
            # The later loop must reuse this independently constructed value,
            # including zero, instead of relying on a desired bit equation.
            rewritten=dict(assignment)
            rewritten.update({column:(magnitude>>i)&1 for i,column in enumerate(recipe['bits'])})
            self.assertEqual(rewritten,assignment)
            wrong=dict(assignment)
            wrong.update({column:((magnitude+1)>>i)&1 for i,column in enumerate(recipe['bits'])})
            evaluate=lambda terms:sum(wrong.get(c,0)*int(v,16) for c,v in terms)%relation.MODULUS
            self.assertTrue(any(evaluate(row['a'])**2%relation.MODULUS!=evaluate(row['b'])
                for row in recipe['raw_rows']))

    def test_no_constructor_target_without_genuine_five_page_qualification(self):
        with self.assertRaises(relation.RelationError):
            sequence.generate(b'{}',[], 'a'*64,{},[],{})

    def test_actual_shared_tables_and_signed_bits_are_kept(self):
        checked,extracted=accepted_fixture()
        owned=local.completion.window_plan(checked,extracted,0,False)
        # One real symbolic local source/row match is sufficient to test the
        # common-support computation; it cannot stand in for a65-loop capture.
        accepted=dict(checked={'chunks':[checked]},protected=owned['protected'],
            programs=[{'writes':owned['writes']}])
        kept=sequence._kept(accepted)
        self.assertTrue({0,1,2,6,16000}<=set(kept))
        self.assertTrue({c for handle in checked['bits'] for c,_ in checked['derived'][handle]}<=set(kept))
        self.assertTrue({c for key in ('base','twice','triple') for value in checked['points'][key]
            for c,_ in checked['derived'][value[1]]}<=set(kept))
        damaged=copy.deepcopy(accepted)
        handle=checked['points']['twice'][0][1]
        damaged['programs'][0]['writes'].append(checked['derived'][handle][0][0])
        with self.assertRaisesRegex(relation.RelationError,'native shared table'):
            sequence._kept(damaged)
        damaged=copy.deepcopy(accepted)
        handle=checked['bits'][10]
        damaged['checked']['chunks'][0]['derived'][handle]=((12000,1),)
        with self.assertRaisesRegex(relation.RelationError,'contiguous singleton'):
            sequence._kept(damaged)
        with self.assertRaisesRegex(relation.RelationError,'all actual windows'):
            sequence._render(accepted,kept,1000)

    def test_default_balance_program_body_stays_byte_identical(self):
        path=Path('.work/diagnostics/transfer-implementation-20261002/balance-variable-native-source-03/source/circuits/generate_transfer_balance_variable_completion.py')
        if not path.exists():self.skipTest('retained exact source unavailable')
        spec=importlib.util.spec_from_file_location('circuits._before_variable_sequence',path)
        before=importlib.util.module_from_spec(spec);spec.loader.exec_module(before)
        checked,extracted=accepted_fixture()
        self.assertEqual(before.render_program(checked,extracted,0,compiler_origin=1000),
            local.render_program(checked,extracted,0,compiler_origin=1000))
        plan=local.completion.window_plan(checked,extracted,0,False)
        with self.assertRaisesRegex(relation.RelationError,'kept/write source separation'):
            local.render_program(checked,extracted,0,compiler_origin=1000,
                sequence_kept=[plan['writes'][0]])


if __name__=='__main__':unittest.main()
