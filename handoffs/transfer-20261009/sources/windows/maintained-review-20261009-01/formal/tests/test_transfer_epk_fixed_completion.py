"""Tiny original-row ownership adapter tests; runtime EPK capture remains UNRUN."""
import copy,unittest
from circuits import transfer_epk_fixed as epk,transfer_epk_fixed_completion as completion,transfer_relation as relation
from tests.test_transfer_epk_fixed import fixture,encoded

def selected_fixture():
    obj,capsules,caller=fixture();checked=epk.inspect_recovery_page(encoded(obj),capsules,caller)
    required,products,squares=completion.requirements(checked)
    # This separate synthetic native-identity table folds all arithmetic. It
    # tests only exact Boolean/copy row ownership, not lawful SPEND_AUTH or EPK.
    assert products==[] and squares==[]
    extraction=dict(metadata_sha256=checked['metadata_sha256'],include_canonical=False,
        identity={'relation_digest':obj['relation_digest'],'domain_size':obj['domain_size'],'stored_rows':obj['full_rows']},
        selected_rows=[{'row':i,'a':[[c,f'{v:064x}'] for c,v in a],'b':[[c,f'{v:064x}'] for c,v in b]}
            for i,(a,b) in enumerate(required)])
    return checked,extraction,capsules,caller
class EpkFixedCompletionTests(unittest.TestCase):
    def test_actual_row_plan_protects_bits_public_committed_and_capsule(self):
        checked,extraction,capsules,caller=selected_fixture()
        plan=completion.completion_plan(checked,extraction,capsules,caller,readonly_lcs=(((6,1),),))
        self.assertEqual(plan['writes'],[])
        self.assertTrue({0,1,2,6,200692,13,14,407}<=set(plan['kept']))
        self.assertEqual(set(plan['original_rows']),set(plan['initial_rows']))
        # Four independent Boolean assignments satisfy every retained original
        # row; caller/public/committed values can be arbitrary.
        for low,high in [(0,0),(1,0),(0,1),(1,1)]:
            assignment={0:1,200692:1,13:low,14:high,1:29,2:31,6:37}
            for row in extraction['selected_rows']:
                values=[sum(assignment.get(c,0)*int(v,16) for c,v in row[axis])%relation.MODULUS for axis in ('a','b')]
                self.assertEqual(values[0]*values[0]%relation.MODULUS,values[1])
    def test_missing_original_boolean_or_copy_refuses(self):
        for drop in range(3):
            checked,extraction,capsules,caller=selected_fixture();extraction['selected_rows'].pop(drop)
            with self.assertRaises(relation.RelationError):completion.completion_plan(checked,extraction,capsules,caller)
    def test_wrong_identity_extra_row_or_old_spend_canonical_mode_refuses(self):
        for change in ('digest','canonical','extra','metadata'):
            checked,extraction,capsules,caller=selected_fixture()
            if change=='digest':extraction['identity']['relation_digest']='f'*64
            elif change=='canonical':extraction['include_canonical']=True
            elif change=='metadata':extraction['metadata_sha256']='e'*64
            else:extraction['selected_rows'].append({'row':900,'a':[[7,f'{1:064x}']],'b':[]})
            with self.subTest(change=change),self.assertRaises(relation.RelationError):completion.completion_plan(checked,extraction,capsules,caller)