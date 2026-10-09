"""Tiny source/typed-operand controls, not a Rust refinement proof."""
import copy
import json
import unittest
from pathlib import Path
from circuits import transfer_compiler_layout as layout
from circuits.transfer_relation import RelationError


class CompilerLayoutTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        source=Path('C:/src/shieldd-pr160-844389ee')
        cls.sources={path:(source/path).read_bytes() for path in layout.SOURCE_CONTRACTS}

    def fixture(self):
        accepted=dict(relation_digest='a'*64,domain_size=262144,full_rows=200770,
            ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True)
        shape=dict(schema='shieldd-transfer-ordered-spool-v1',public_inputs=1,blocks=[1],
            source_public=[[1,22734]],source_blocks=[[[1,6]]],relation_digest='a'*64,
            domain_size=262144,full_rows=200770)
        shapes=[dict(shape,compilation=kind) for kind in ('ordinary','ordinary','observer','observer')]
        return accepted,shapes

    def derive(self,accepted,shapes,sources=None):
        return layout.derive_layout(accepted,[(json.dumps(shape)+'\n').encode() for shape in shapes],
            self.sources if sources is None else sources)

    def test_symbolic_tail_count_and_column_layout(self):
        result=self.derive(*self.fixture())
        self.assertEqual((result['last_witness_index'],result['witness_count'],result['product_origin']),
            (22734,22735,22738))
        self.assertIn('correspondence remain separate',result['scope'])

    def test_false_acceptance_or_changed_layout_refuses(self):
        for target in ('flag','public','block','identity','unknown','boolean'):
            accepted,shapes=self.fixture()
            if target=='flag':accepted['repeated_observations_equal']=False
            if target=='public':shapes[-1]['source_public']=[[1,22733]]
            if target=='block':shapes[-1]['source_blocks']=[[[1,7]]]
            if target=='identity':shapes[-1]['relation_digest']='b'*64
            if target=='unknown':shapes[-1]['witnesses']=22735
            if target=='boolean':shapes[-1]['source_blocks']=[[[True,6]]]
            with self.subTest(target=target),self.assertRaises(RelationError):self.derive(accepted,shapes)

    def test_reviewed_guard_and_source_identity_are_both_checked(self):
        accepted,shapes=self.fixture();path='crates/crypto/circuits/src/transfer.rs'
        changed=copy.copy(self.sources)
        changed[path]=changed[path].replace(b'let claimed = var(claimed_statement);',
            b'let claimed = var(claimed_statement); let extra = var(claimed_statement);')
        with self.assertRaises(RelationError):self.derive(accepted,shapes,changed)
        changed[path]=self.sources[path]+b'\n// identity-only mutation\n'
        with self.assertRaisesRegex(RelationError,'source identity'):self.derive(accepted,shapes,changed)


if __name__=='__main__':unittest.main()
