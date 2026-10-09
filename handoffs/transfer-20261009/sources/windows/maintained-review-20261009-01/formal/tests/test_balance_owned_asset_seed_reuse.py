"""Source-level owned reseed correspondence; no runtime certificate generation."""
from pathlib import Path
import re
import unittest
from circuits import generate_transfer_balance_asset_seed_reuse as renderer
from circuits.transfer_relation import RelationError

P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
S=P/'windows-jubjub-isolated-05/ShielddSecurity'
ACTUAL='RuntimeHashBlock_balance0_asset0_permutation0_0'
NATIVE='RuntimeHashBlock_authorization_rnk_permutation2_0'

class BalanceOwnedAssetSeedReuseTests(unittest.TestCase):
    def test_default_body_exactly_preserved(self):
        path=P/'balance-asset-seed-reuse-source-01/source/circuits/generate_transfer_balance_asset_seed_reuse.py'
        legacy={'__name__':'circuits.legacy_asset_seed_renderer','__package__':'circuits'}
        exec(compile(path.read_bytes(),str(path),'exec'),legacy)
        for left,right in [('a'*64,'b'*64),('0'*64,'f'*64)]:
            self.assertEqual(renderer._source(left,right,[190237,190241]),
                             legacy['_source'](left,right,[190237,190241]))

    def test_actual_full_signed_parameter_declarations_and_refusals(self):
        actual=(S/'RuntimeTransferActualAssetHashBlock0_Data.lean').read_text()
        native=(S/'RuntimeRnkHash2_Data.lean').read_text()
        a=renderer._parameter_declaration(actual,ACTUAL)
        n=renderer._parameter_declaration(native,NATIVE)
        self.assertEqual(a,n)
        renderer._check_parameter_correspondence(actual,native)
        self.assertIn('ark :=',a)
        self.assertIn('mds :=',a)
        for token in ('ark :=','mds :='):
            offset=a.index(token)
            number=re.search(r'-?\d{10,}',a[offset:])
            self.assertIsNotNone(number)
            start=offset+number.start();end=offset+number.end()
            changed=a[:start]+str(int(a[start:end])+1)+a[end:]
            with self.assertRaises(RelationError):
                renderer._check_parameter_correspondence(actual.replace(a,changed),native)
        with self.assertRaises(RelationError):
            renderer._check_parameter_correspondence(
                actual.replace('| _ => fun _ => 0','| _ => fun _ => 1',1),native)
        for bad,namespace in [(actual,NATIVE),(actual+'\naxiom bad : True\n',ACTUAL),
                              (actual.replace('def parameters :','def omitted :'),ACTUAL)]:
            with self.assertRaises(RelationError):renderer._parameter_declaration(bad,namespace)

    def test_owned_source_uses_literal_program_same_object_and_all_global_laws(self):
        name,legacy=renderer._source('a'*64,'b'*64,[190237,190241])
        owned,body=renderer._owned_source(name,legacy)
        self.assertEqual(owned,'RuntimeBalanceOwnedAssetSeedReuse')
        self.assertNotIn('HashMapABI',body)
        self.assertNotIn('NativeAssetValueGenerator.',body)
        self.assertEqual(body.count('NativeAssetGeneratorSource.valueGenerator hex fq arithmetic initial square sdkApi ops upstream points asset'),6)
        self.assertIn('let sourceRho := RuntimeTransferAssetNonzero.completeAssignment',body)
        self.assertIn('NativeAssetGeneratorSource.coordinates hex fq arithmetic initial square codec',body)
        self.assertNotIn('let initial :=',body)
        self.assertIn('RuntimeElligatorParameters.negative_z_nonsquare',body)
        self.assertIn('RuntimeTransferAssetMapNativeSeeds.five_euler cardinality',body)
        self.assertIn('coefficient_k',body)
        self.assertIn('coefficient_c1',body)
        self.assertIn('coefficient_c2',body)
        self.assertNotRegex(body,r'\b(?:sorry|admit|native_decide|axiom)\b')
        names=re.findall(r'^#print axioms (\w+)$',body,re.M)
        self.assertEqual(len(names),8)
        self.assertEqual(names,re.findall(r'^#check @(\w+)$',body,re.M))
        self.assertIn('source_input',names)
        self.assertIn('reseed_unchanged',names)
        with self.assertRaises(RelationError):renderer._owned_source(name,legacy.replace('theorem source_input ','theorem altered '))
