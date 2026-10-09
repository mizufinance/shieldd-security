"""Actual source-polynomial/row-backed local signed balance assignments."""
import copy,json,re,unittest
from circuits import transfer_signed_balance_completion as completion,transfer_relation as relation
from circuits import generate_transfer_signed_balance_completion as generator
from tests import test_transfer_balance_rows as fixtures


class SignedBalanceCompletionTests(unittest.TestCase):
    def setUp(self):
        self.fixture=fixtures.BalanceRowTests();self.fixture.setUp()
        self.checked=self.fixture.run_fixture()
        self.metadata=copy.deepcopy(self.fixture.metadata)
        self.metadata.update(relation_digest=self.checked['identity']['relation_digest'],stored_rows=len(self.fixture.rows))
        self.bytes=(json.dumps(self.metadata)+'\n').encode()
        self.recipe=completion._from_checked(self.bytes,self.checked)

    def test_all_original_signed_rows_both_signs_and129bit_boundary(self):
        limit=2**128
        for amounts in ([0,0,0,0],[7,3,4,1],[3,2,9,1],[limit-1,limit-1,0,0],
                        [0,0,limit-1,limit-1],[limit-1,1,limit-1,1]):
            base={0:1,self.recipe['copy']:1,1:101,2:103,1000:107}
            base.update(zip(self.recipe['amounts'],amounts))
            base.update({c:(c*19+13)%completion.P for c in self.recipe['owned_writes']})
            built=completion.construct(self.recipe,base,amounts);rho=built['assignment']
            self.assertEqual(len(built['original_rows_satisfied']),135)
            self.assertEqual(len(built['owned_writes']),133)
            net=amounts[0]+amounts[1]-amounts[2]-amounts[3]
            self.assertEqual(-built['magnitude'] if built['negative'] else built['magnitude'],net)
            self.assertEqual(sum(rho[c]<<i for i,c in enumerate(self.recipe['bits'])),abs(net))
            for c,value in base.items():
                if c not in built['owned_writes']:self.assertEqual(rho[c],value)
            # Independent evaluator checks every original encoded row, rather
            # than comparing renderer text or just a construction receipt.
            evaluate=lambda terms:sum(rho.get(c,0)*int(v,16) for c,v in terms)%completion.P
            for row in self.recipe['raw_rows']:
                self.assertEqual(evaluate(row['a'])**2%completion.P,evaluate(row['b']))

    def test_source_identity_shared_freshness_and_native_input_refusal(self):
        metadata=copy.deepcopy(self.metadata);metadata['constant_copy']+=1
        with self.assertRaises(relation.RelationError):completion._from_checked((json.dumps(metadata)+'\n').encode(),self.checked)
        damaged=copy.deepcopy(self.checked)
        damaged['selected_rows']=[row for row in damaged['selected_rows'] if row['row']!=self.recipe['original_row_indices'][-1]]
        with self.assertRaises((relation.RelationError,KeyError)):completion._from_checked(self.bytes,damaged)
        base={0:1,self.recipe['copy']:1,**dict(zip(self.recipe['amounts'],[1,2,3,4]))}
        for amounts in ([1,2,3,2**128],[1,2,3,True],[1,2,3,5]):
            with self.assertRaises(relation.RelationError):completion.construct(self.recipe,base,amounts)
        base[self.recipe['copy']]=0
        with self.assertRaises(relation.RelationError):completion.construct(self.recipe,base,[1,2,3,4])

    def test_symbolic_range_owned_product_and_original_row_renderer(self):
        name,source=generator._from_checked(self.recipe)
        self.assertEqual(name,'RuntimeTransferSignedBalanceCompletion')
        self.assertEqual(len(re.findall(r'#check @',source)),15)
        self.assertEqual(re.findall(r'#check @([A-Za-z0-9_]+)',source),re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertIn('writeBits_range_complete',source)
        self.assertIn('ScalarBitFootprint.initial_rows_below',source)
        self.assertIn('CompilerSignedCompletion.original_rows',source)
        self.assertIn('TransferSignedMagnitude.field_equation',source)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        declaration=source[source.index('theorem original_rows_complete'):].split(':=',1)[0]
        for forbidden in ('(satisfied','(signedEquation','(magnitudeBound','(negativeValue','(inverseEquation'):
            self.assertNotIn(forbidden,declaration)
        self.assertIn('(nativeAmounts : ∀ i, rho (amountColumns i) = ((amounts i).val : F))',declaration)
        self.assertNotIn('fin_cases',source)
        self.assertNotIn('![',source)
        self.assertIn('⟨Compiler.subtract difference selected,[]⟩,⟨[],[]⟩]',source)
        self.assertIn('List.mem_cons,List.not_mem_nil,or_false] at written',source)

    def test_constant_copy_unoutline_and_exact_boundary_semantics(self):
        recipe=copy.deepcopy(self.recipe)
        by_index={row['row']:row for row in recipe['raw_rows']}
        link=by_index[recipe['roles']['constant-copy']]
        canonical=completion.balance.canonical
        self.assertEqual(canonical((0 if c==recipe['copy'] else c,int(v,16)) for c,v in link['a']),())
        # The original signed assertion may be stored in either square sign;
        # the independently retained source selection remains the same.
        signed=by_index[recipe['roles']['signed.equation']]
        signed['a']=[[c,f'{(-int(v,16))%completion.P:064x}'] for c,v in signed['a']]
        generator._from_checked(recipe)
        for key in ('constant-copy','signed.equation'):
            damaged=copy.deepcopy(self.recipe)
            actual=next(row for row in damaged['raw_rows'] if row['row']==damaged['roles'][key])
            c,v=actual['a'][0];actual['a'][0]=[c,f'{(int(v,16)+1)%completion.P:064x}']
            with self.assertRaisesRegex(relation.RelationError,'boundary row has no exact unoutlined correspondence'):
                generator._from_checked(damaged)


if __name__=='__main__':unittest.main()
