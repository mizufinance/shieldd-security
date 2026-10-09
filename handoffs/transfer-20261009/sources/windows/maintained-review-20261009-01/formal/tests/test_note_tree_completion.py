"""Exact tree ownership and constructive four-position row semantics."""
import copy,io,unittest
from circuits import generate_note_tree_completion as complete,transfer_note_tree as tree
from circuits import transfer_relation as relation
from tests.test_note_tree import tree_fixture
from tests.test_transfer_note_spend import encoded


class NoteTreeCompletionTests(unittest.TestCase):
    def fixture(self,slot=0,level=0):
        obj,note,caller,stream,_=tree_fixture();data=encoded(obj)
        extracted=tree.extract_level(data,io.BytesIO(stream.getvalue()),note,caller,slot,level)
        return data,extracted,note,caller

    def test_construct_all_positions_preserve_shared_and_every_other_column(self):
        data,extracted,note,caller=self.fixture();plan=complete.completion_plan(data,extracted,note,caller)
        self.assertEqual(len(plan['writes']),12)
        self.assertFalse(set(plan['writes'])&set(plan['kept']))
        p=relation.MODULUS
        for position in range(4):
            rho={c:(31*c+11)%p for c in range(4096)};rho[0]=rho[4000]=1
            for name,bit in (('low',position%2),('high',position//2)):
                column,coefficient=plan['current'][name][0];self.assertEqual(coefficient,1);rho[column]=bit
            before=dict(rho);evaluate=lambda terms:sum(rho[c]*v for c,v in terms)%p
            node=evaluate(plan['current']['node']);expected=[evaluate(lc) for lc in plan['current']['siblings']]
            expected.insert(position,node)
            for step in plan['steps']:
                left,right=evaluate(step['left']),evaluate(step['right']);remainder=evaluate(step['remainder'])
                rho[step['output']]=(left*right-remainder)%p;rho[step['auxiliary']]=(left-right)**2%p
            self.assertEqual([evaluate(lc) for lc in plan['current']['children']],expected)
            self.assertTrue(all(evaluate(a)**2%p==evaluate(b) for a,b in plan['selected']['raw'].values()))
            self.assertTrue(all(rho[c]==before[c] for c in before if c not in plan['writes']))
            rho[plan['writes'][0]]=(rho[plan['writes'][0]]+1)%p
            self.assertFalse(all(evaluate(a)**2%p==evaluate(b) for a,b in plan['selected']['raw'].values()))

    def test_first_last_both_notes_have_coverage_and_independent_bit_meanings(self):
        for slot,level in ((0,0),(0,23),(1,0),(1,23)):
            modules=complete.generate(*self.fixture(slot,level));source=modules[1][1]
            self.assertEqual(source.count('#print axioms'),9)
            self.assertIn('CompilerOrder.checked_order',source)
            self.assertIn('coverage_checked',source)
            signature=source[source.index('theorem complete_level'):source.index(' := by',source.index('theorem complete_level'))]
            self.assertNotIn('(satisfied :',signature)
            self.assertNotIn('childrenEquation',signature)
            self.assertIn('lowValue : eval rho low = Tree.bit lo',signature)

    def test_prior_caller_owned_pivot_refused(self):
        data,extracted,note,caller=self.fixture();changed=copy.deepcopy(caller)
        changed['observed'][(2,9999)]=((2500,1),)
        with self.assertRaisesRegex(relation.RelationError,'shared or prior'):
            complete.completion_plan(data,extracted,note,changed)


if __name__=='__main__':unittest.main()
