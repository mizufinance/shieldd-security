import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from integration import transfer_balance_actual_spec as spec
from circuits import transfer_ivk_rows,transfer_ivk_reduction,transfer_ownership,transfer_authorization_roles
from circuits.transfer_relation import RelationError


class NativeCallerSpecTests(unittest.TestCase):
    def test_refuses_claimed_serialized_acceptance_instead_of_parser_recipe(self):
        with self.assertRaisesRegex(RelationError,'closed actual caller parser recipe'):
            spec.restore_caller({'metadata':{'ordinary_full_ordered_rows_equal':True},'observed':{}},{})

    def test_reconstructs_tuple_keyed_lcs_through_all_four_independent_parsers(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary)
            paths={name:root/name for name in ('ivk','reduction','rnk','roles','poseidon381.json','poseidon381-wide.json')}
            for path in paths.values():path.write_bytes(b'fixture metadata bytes')
            recipe=dict(schema=spec.SCHEMA,parameters=spec.path_text(root),
                **{name:spec.path_text(paths[name]) for name in ('ivk','reduction','rnk','roles')})
            pins={spec.path_text(path):spec.sha(path) for path in paths.values()}
            actual={ 'observed':{(1,3):((6,1),)},'metadata':{} }
            with patch.object(transfer_ivk_rows,'inspect_metadata',return_value={'metadata':{'handles':[]}}) as ivk, \
                 patch.object(transfer_ivk_reduction,'inspect_metadata',return_value={'metadata':{'remainder_bits':[],'remainder':0}}) as reduction, \
                 patch.object(transfer_ownership,'inspect_rnk_metadata',return_value={'metadata':{}}) as rnk, \
                 patch.object(transfer_authorization_roles,'inspect_metadata',return_value=actual) as roles:
                self.assertIs(spec.restore_caller(recipe,pins),actual)
                self.assertIn((1,3),actual['observed'])
                for parser in (ivk,reduction,rnk,roles):parser.assert_called_once()
                paths['roles'].write_bytes(b'changed')
                with self.assertRaisesRegex(RelationError,'must be pinned'):spec.restore_caller(recipe,pins)
                for parser in (ivk,reduction,rnk,roles):parser.assert_called_once()

    def test_builder_refuses_missing_genuine_inputs_before_creating_output(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);output=root/spec.INPUT_PACKET
            with self.assertRaisesRegex(RelationError,'real qualified parent'):spec.build(root,output)
            self.assertFalse(output.exists())
