"""Small source-boundary refusals; fixtures confer no runtime/kernel credit."""
import copy,unittest
from unittest.mock import patch
from circuits import generate_transfer_epk_fixed_template_trace_page as emit
from circuits.transfer_relation import RelationError
from tests.test_generate_transfer_epk_fixed_template import fixture


class TemplateTracePageTests(unittest.TestCase):
    def fixture(self):
        checked,raw,normal,plan=fixture()
        bounds=dict(constant_copy=1000,high_start=201,frames=[None,
            dict(index=1,before=dict(low=60,high=201),after=dict(low=62,high=216))])
        return (checked,raw,normal,{}, {},plan,'RuntimeTransferEpk0FixedWindow001'),dict(bounds=bounds)

    def test_full_union_acceptance_precedes_exact_fixed_projection(self):
        selection,accepted=self.fixture()
        union={'fixed':{'actual':'fixed projection'},'canonical':{'actual':'scalar projection'}}
        calls=[]
        def accept_full(*args):
            calls.append(('full',args));return accepted
        def accept_page(*args):
            calls.append(('page',args));return selection
        with patch.object(emit.full,'plan',side_effect=accept_full),patch.object(emit.ingress,'_selection',side_effect=accept_page):
            modules=emit.generate_modules(b'parent',[],{}, {},union,0,1)
        self.assertEqual([kind for kind,_ in calls],['full','page'])
        self.assertIs(calls[0][1][4],union)
        self.assertIs(calls[1][1][4],union['fixed'])
        self.assertEqual([name for name,_ in modules],[
            'RuntimeTransferEpk0FixedWindow001TemplateTrace','RuntimeTransferEpk0FixedTemplatePage01Trace'])

    def test_copy_frame_and_protected_write_refusals(self):
        for mutation,expected in (('copy','constant copy'),('frame','allocation frame'),('protected','alias')):
            selection,accepted=self.fixture();selection=copy.deepcopy(selection)
            if mutation=='copy':accepted['bounds']['constant_copy']=999
            elif mutation=='frame':accepted['bounds']['frames'][1]['index']=2
            else:selection[5]['kept'].append(60)
            with patch.object(emit.full,'plan',return_value=accepted),patch.object(emit.ingress,'_selection',return_value=selection):
                with self.subTest(mutation=mutation),self.assertRaisesRegex(RelationError,expected):
                    emit.generate_modules(b'parent',[],{}, {},{'fixed':{}},0,1)

    def test_page_preserves_incoming_coordinates_omitted_from_caller_set(self):
        selection,accepted=self.fixture()
        selection[5]['kept']=[c for c in selection[5]['kept'] if c not in (30,31)]
        with patch.object(emit.full,'plan',return_value=accepted),patch.object(emit.ingress,'_selection',return_value=selection):
            modules=emit.generate_modules(b'parent',[],{}, {},{'fixed':{}},0,1)
        # The page entry consumes a previous constructor's output. It must
        # remain protected even when it is absent from the caller read set.
        for _,source in modules:
            self.assertIn('def kept : List Nat := [0, 1, 2, 11, 12, 30, 31, 1000]',source)


if __name__=='__main__':unittest.main()
