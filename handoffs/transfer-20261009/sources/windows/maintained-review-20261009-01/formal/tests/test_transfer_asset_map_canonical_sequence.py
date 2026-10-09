"""Actual numeric/canonical phase composition and original-row preservation."""
import io
import re
import unittest
from pathlib import Path
from unittest.mock import patch
from circuits import transfer_asset_map as maps,transfer_asset_map_canonical_sequence as sequence
from circuits import transfer_asset_map_completion as completion,transfer_relation as relation
from tests.test_transfer_asset_map import fixture
from tests.test_asset_asserted_squares import defer_captured


def deferred_sequence_fixture():
    data,caller,stream,_,builder=fixture(17)
    data,caller,raw,builder=defer_captured(data,caller,stream.getvalue(),builder)
    return data,caller,io.BytesIO(raw),builder


class CanonicalSequenceTests(unittest.TestCase):
    def test_original858_rows_from_arbitrary_kept_seeds_and_canonical_value(self):
        data,caller,stream,builder=deferred_sequence_fixture()
        extracted=maps.extract(data,stream,caller);recipe=sequence.plan(data,extracted,caller)
        self.assertEqual((len(recipe['before']),len(recipe['canonical']['steps']),len(recipe['after'])),(8,254,42))
        self.assertEqual(len(recipe['original_indices']),858)
        self.assertLessEqual(len(recipe['exceptions']),8)
        for value in (0,1,maps.P-1):
            base=dict(builder.rho)
            base.update({c:19*c+37 for c in recipe['recipe']['owned_writes']})
            base.update({1:83,2:97,32767:113})
            built=sequence.construct(data,extracted,caller,base,value);rho=built['assignment']
            evaluate=lambda lc:sum(rho.get(c,0)*n for c,n in lc)%maps.P
            self.assertTrue(all(evaluate(recipe['recipe']['raw'][i][0])**2%maps.P==evaluate(recipe['recipe']['raw'][i][1])
                                for i in recipe['original_indices']))
            self.assertEqual(evaluate(recipe['recipe']['checked']['canonical'][1]),1)
            self.assertEqual([rho[c] for c in (0,1,2,32000,32767)],[1,83,97,1,113])
            self.assertTrue(all(rho.get(c,0)==v for c,v in base.items() if c not in built['owned']))
            self.assertTrue(all(rho[c]==base[c] for label,c in recipe['recipe']['seeds'].items()
                                if label!='selectedRoot' and not label.startswith('bit')))
            # The unconstructed12 native assertions still fail arbitrary seeds.
            self.assertTrue(any(evaluate(a)**2%maps.P!=evaluate(b)
                                for i,(a,b) in recipe['recipe']['raw'].items() if i not in recipe['original_indices']))
            self.assertFalse(built['proof'])

    def test_freshness_and_symbolic_patch_commutation_are_explicit(self):
        data,caller,stream,_=deferred_sequence_fixture()
        extracted=maps.extract(data,stream,caller);recipe=completion.plan(data,extracted,caller)
        name,source=sequence.generate(data,extracted,caller)
        self.assertEqual(name,'RuntimeTransferAssetMapCanonicalSequence')
        audits=re.findall(r'#check @([A-Za-z0-9_]+)',source)
        self.assertEqual(len(audits),13)
        self.assertEqual(audits,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertIn('CompilerPatchCommutation.run_commutes',source)
        self.assertIn('CompilerSequenceCompletion.preserves_rows',source)
        self.assertIn('program_split',source)
        complete=source[source.index('theorem complete_rows'):]
        self.assertNotIn('(satisfied',complete[:complete.index(':=')])
        helper=(Path(__file__).resolve().parents[1]/'circuits/ShielddSecurity/CompilerPatchCommutation.lean').read_text()
        self.assertEqual(re.findall(r'#check @([A-Za-z0-9_]+)',helper),re.findall(r'#print axioms ([A-Za-z0-9_]+)',helper))
        self.assertEqual(helper.count('#check @'),6)
        self.assertIn('List.mem_range\'_1.mpr inside',helper)
        self.assertIn('List.mem_range\'_1.mp member',helper)
        self.assertIn('List.mem_cons,List.not_mem_nil,or_false] at member',helper)
        self.assertIn('rcases member with atOutput | atAuxiliary',helper)
        self.assertIn('by_cases atOutput : column = output',helper)
        self.assertNotIn('rcases member with rfl | rfl',helper)
        self.assertIn('atRoot,member,false_or,if_true,if_false]',helper)
        for text in (source,helper):self.assertNotRegex(text,r'\b(sorry|admit|axiom|native_decide)\b')
        altered=dict(recipe,steps=[*recipe['steps'][:1],dict(recipe['steps'][1],left=recipe['checked']['values']['y']),*recipe['steps'][2:]])
        with patch.object(completion,'plan',return_value=altered):
            with self.assertRaisesRegex(relation.RelationError,'before phase reads/writes'):
                sequence.plan(data,extracted,caller)

    def test_materialized_root_square_before_bits_is_refused(self):
        data,caller,stream,_,_=fixture(17)
        extracted=maps.extract(data,stream,caller)
        with self.assertRaisesRegex(relation.RelationError,'before phase reads/writes native root bits'):
            sequence.plan(data,extracted,caller)


if __name__=='__main__':unittest.main()
