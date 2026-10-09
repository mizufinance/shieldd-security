"""One strict acceptance per bounded mathematical page fixture, no capture."""
import unittest
from unittest.mock import patch
from circuits import generate_transfer_epk_fixed_template_page as emit
from circuits.transfer_relation import RelationError
from tests.test_generate_transfer_epk_fixed_template import fixture

class TemplatePageTests(unittest.TestCase):
    def test_one_ingress_acceptance_and_topological_modules(self):
        checked,raw,normal,plan=fixture()
        selected=(checked,raw,normal,{}, {},plan,'RuntimeTransferEpk0FixedWindow001')
        with patch.object(emit.ingress,'_selection',return_value=selected) as accept:
            result=emit.generate_modules(b'parent',[],{}, {},{},0,1)
        accept.assert_called_once_with(b'parent',[],{}, {},{},0,1,0,())
        self.assertEqual([name for name,_ in result],[
            'RuntimeTransferEpk0FixedWindow001TemplateCompletion','RuntimeTransferEpk0FixedWindow001TemplateProgram'])

    def test_mismatched_namespace_and_page_bound_refuse(self):
        for mutation in ('namespace','missing_fixed','bound'):
            checked,raw,normal,plan=fixture()
            stem='RuntimeTransferEpk0FixedWindow001'
            if mutation=='namespace':stem='RuntimeTransferEpk0FixedWindow002'
            elif mutation=='missing_fixed':stem='RuntimeTransferEpk0Window001'
            else:plan['window_count']=17
            with patch.object(emit.ingress,'_selection',return_value=(checked,raw,normal,{}, {},plan,stem)):
                with self.subTest(mutation=mutation),self.assertRaises(RelationError):
                    emit.generate_modules(b'parent',[],{}, {},{},0,1)

if __name__=='__main__':unittest.main()
