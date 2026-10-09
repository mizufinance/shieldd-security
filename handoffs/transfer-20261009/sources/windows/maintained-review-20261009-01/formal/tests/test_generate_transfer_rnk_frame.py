"""Small generated-source shape controls; fixture declarations are unqualified."""
import re
import unittest
from circuits.generate_transfer_rnk_frame import (generate_hash_data_coverage,generate_ownership_window_coverage,
    generate_declared_rows_coverage,generate_aggregate_coverage,extend_rk_support)
from circuits.transfer_relation import RelationError


def fixture():
    namespace='RuntimeHashBlock_authorization_rnk_permutation0_0'
    return ('namespace ShielddSecurity.'+namespace+'\n'+
        'def rawRoundRows : Nat → List Row := fun index => match index with\n'+
        ''.join(f'  | {i} => []\n' for i in range(65))+'  | _ => []\n'+
        'def rawRows : List Row := (List.range 65).flatMap rawRoundRows\n'+
        'end ShielddSecurity.'+namespace+'\n').encode()


class RnkFrameTests(unittest.TestCase):
    def generate(self,data=None,**kw):
        return generate_hash_data_coverage('RuntimeRnkHash0_Data',fixture() if data is None else data,
            origin=22738,copy=200692,frame=[4271,64440],**kw)

    def test_each_small_round_once_and_symbolic_group_join(self):
        modules=self.generate()
        self.assertEqual(len(modules),14)
        joined=''.join(modules.values())
        checks=re.findall(r'#check @([A-Za-z0-9_]+)',joined)
        self.assertEqual(checks,re.findall(r'#print axioms ([A-Za-z0-9_]+)',joined))
        rounds=re.findall(r'private theorem round([0-9]+)',joined)
        self.assertEqual([int(x) for x in rounds],list(range(65)))
        for name,source in modules.items():
            self.assertLessEqual(source.count('private theorem round'),5)
            self.assertNotRegex(source,r'\b(sorry|admit|axiom)\b')
            self.assertNotIn('abbrev Data',source)
            self.assertNotIn('namespace Data :=',source)
        self.assertIn('CompilerFrameCoverage.grouped_flat_map',modules['RuntimeRnkHash0_FrameAll'])

    def test_missing_or_reordered_round_and_namespace_refuse(self):
        for data in (fixture().replace(b'  | 0 => []\n',b''),
                     fixture().replace(b'  | 0 => []',b'  | 1 => []'),
                     fixture().replace(b'permutation0_0',b'permutation1_0')):
            with self.assertRaises(RelationError):self.generate(data)

    def test_small_chunk_bound_refuses_boolean_or_wide(self):
        for chunk in (True,0,6):
            with self.assertRaises(RelationError):self.generate(chunk_size=chunk)

    def test_ivk_rounds_reuse_same_bounded_checker(self):
        data=fixture().replace(b'RuntimeHashBlock_authorization_rnk_permutation0_0',
            b'RuntimeHashBlock_authorization_ivk_0')
        modules=generate_hash_data_coverage('RuntimeIvkHash_Data',data,origin=22738,copy=200692,frame=[4271,64440])
        self.assertEqual(len(modules),14)
        self.assertIn('RuntimeIvkHash_FrameAll',modules)

    def test_ownership_existing_main_rows_are_checked(self):
        name='RuntimeOwnershipWindow000'
        source=('namespace ShielddSecurity.'+name+'\ndef rawRows : List Row := []\n'+
            'end ShielddSecurity.'+name+'\n').encode()
        modules=generate_ownership_window_coverage(name,source,origin=22738,copy=200692,frame=[4271,64440])
        candidate=modules[name+'_Frame']
        self.assertIn(name+'.rawRows',candidate)
        self.assertEqual(candidate.count('#check @'),1)
        with self.assertRaises(RelationError):generate_ownership_window_coverage(name,source.replace(b'rawRows',b'otherRows'),
            origin=22738,copy=200692,frame=[4271,64440])

    def test_original_named_blocks_refuse_missing_ambiguous_or_unclosed(self):
        name='RuntimeTransferQuotient'
        data=('namespace ShielddSecurity.'+name+'\ndef originalRows : List Row := []\n'+
            'end ShielddSecurity.'+name+'\n').encode()
        kw=dict(declarations=['originalRows'],origin=22738,copy=200692,frame=[4271,64440])
        modules=generate_declared_rows_coverage(name,data,**kw)
        self.assertIn(name+'.originalRows',next(iter(modules.values())))
        for bad in (data.replace(b'originalRows',b'otherRows'),data.replace(b'def originalRows',
                b'def originalRows : List Row := []\ndef originalRows'),data.split(b'end ')[0]):
            with self.assertRaises(RelationError):generate_declared_rows_coverage(name,bad,**kw)
        with self.assertRaises(RelationError):generate_declared_rows_coverage(name,data,
            **dict(kw,declarations=[[]]))

    def test_aggregate_uses_imported_certificates_without_row_truth_premise(self):
        specs=[dict(proof_module='FixtureProof',rows='Fixture.rows',proof='FixtureProof.rows_covered')]
        kw=dict(origin=22738,copy=200692,frame=[4271,64440])
        source=next(iter(generate_aggregate_coverage(specs,**kw).values()))
        self.assertIn('CompilerFrameCoverage.CoveredBlock',source)
        self.assertIn('exact block.covered',source)
        self.assertNotIn('Satisfies',source)
        for bad in ([dict(specs[0],proof='FixtureProof.bad; exact False.elim')],
                [dict(specs[0],proof_module='Fixture.Proof')],[] ):
            with self.assertRaises(RelationError):generate_aggregate_coverage(bad,**kw)
        with self.assertRaises(RelationError):generate_aggregate_coverage(specs,**dict(kw,frame=[30000,64440]))

    def test_support_extension_requires_exact_broader_fence_and_six_exports(self):
        base=('namespace ShielddSecurity.RuntimeTransferRkSupport\n'
            'def fixedFrame : GroupFixedCircuitBounds.Frame := ⟨4271,64440⟩\n'
            'def additionFrame : GroupFixedCircuitBounds.Frame := ⟨4272,64462⟩\n'
            '-- GroupFixedCircuitBounds.covers 22738 200692\n'+
            ''.join(f'#check @fixture{i}\n' for i in range(6))+
            'end ShielddSecurity.RuntimeTransferRkSupport\n')
        extended=extend_rk_support(base)
        self.assertEqual(extended.count('#check @'),8)
        self.assertIn('earlier_addition_preserves_support',extended)
        narrower=extend_rk_support(base,prior_frame=[3767,61934])
        self.assertIn('Nat.lt_of_lt_of_le low',narrower)
        self.assertEqual(narrower.count('#check @'),8)
        for frame in ([True,61934],[4272,61934],[3767,64441],[3767,22738]):
            with self.assertRaises(RelationError):extend_rk_support(base,prior_frame=frame)
        for bad in (base.replace('22738','61934'),base.replace('#check @fixture5','-- fixture5')):
            with self.assertRaises(RelationError):extend_rk_support(bad)


if __name__=='__main__':unittest.main()
