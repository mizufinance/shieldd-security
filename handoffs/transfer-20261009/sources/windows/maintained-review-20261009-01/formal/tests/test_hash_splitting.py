import hashlib,re,unittest
from circuits.generate_hash_round import split_block_modules, split_block_data, _signature_audits
from circuits.hash_controls import summary


class HashProofSplitTests(unittest.TestCase):
    """Structural generator controls; no synthetic theorem is proof evidence."""
    def source(self):
        result='import ShielddSecurity.Poseidon\nnamespace Example\ndef literal : Nat := 0\n'
        for i in range(65):
            result+=f'theorem constant_link_{i} : True := by trivial\n'
            result+=f'theorem certificate_{i} : True := by trivial\n'
        return result+'theorem constant_links : True := by trivial\nend Example\n'
    def test_all_rounds_once_with_shared_data_and_symbolic_glue(self):
        parts=split_block_modules(self.source(),'ExampleBlock',5)
        self.assertEqual(len(parts),15)
        self.assertNotIn('theorem',parts[0][1])
        all_chunks=''.join(source for _,source in parts[1:-1])
        for i in range(65):
            self.assertEqual(all_chunks.count(f'theorem certificate_{i} :'),1)
            self.assertEqual(all_chunks.count(f'#check @certificate_{i}\n'),1)
            self.assertEqual(all_chunks.count(f'#print axioms certificate_{i}\n'),1)
        self.assertEqual(parts[-1][1].count('import ShielddSecurity.ExampleBlock_Rounds_'),13)
        self.assertNotIn('theorem certificate_',parts[-1][1])
    def test_bad_ranges_and_incomplete_or_reordered_rounds_fail(self):
        for size in (True,0,9,100):
            with self.assertRaises(ValueError):split_block_modules(self.source(),'ExampleBlock',size)
        for source in (self.source().replace('constant_link_5 :','constant_link_7 :'),
                       self.source().replace('end Example\n','')):
            with self.assertRaises(ValueError):split_block_modules(source,'ExampleBlock')
    def test_control_summary_uses_actual_scope_and_control_counts(self):
        for keys in ([],[{},{}]):
            receipt={'one_positive':True,'round_semantic_controls':[{}]*4,
                     'key_link_controls':keys,'scope':'explicit selected slice'}
            result=summary(receipt)
            self.assertEqual(result['key_link_controls'],len(keys))
            self.assertEqual(result['round_semantic_controls'],4)
            self.assertEqual(result['scope'],receipt['scope'])

    def test_full_signature_commands_emitted_beside_named_axiom_audits(self):
        text=_signature_audits('#print axioms checked\n')
        self.assertIn('set_option pp.all true in\n#check @checked\n#print axioms checked',text)

    def test_optional_literal_partition_preserves_exact_definitions_and_theorems(self):
        literals=''.join(f'def lc_{i} : Linear := [(0, ({i} : Int))]\n' for i in range(97))
        original=self.source().replace('def literal : Nat := 0\n',
            'def modulus : Nat := 7\n'+literals+'\ndef rawRoundRows : Nat → List Row := fun _ => []\n')
        regular=split_block_modules(original,'ExampleBlock')
        split=split_block_modules(original,'ExampleBlock',linear_declarations_per_module=32)
        self.assertEqual([name for name,_ in split[5:]],[name for name,_ in regular[1:]])
        for (_,new),(_,old) in zip(split[5:],regular[1:]):
            scrub=lambda text:re.sub(r'Exact shared data SHA256: [0-9a-f]{64}','Exact shared data SHA256: HASH',text)
            self.assertEqual(scrub(new),scrub(old))
        self.assertIn(hashlib.sha256(split[4][1].encode()).hexdigest(),split[5][1])
        self.assertEqual([name for name,_ in split[:4]],[
            'ExampleBlock_Data_Linear_0_31','ExampleBlock_Data_Linear_32_63',
            'ExampleBlock_Data_Linear_64_95','ExampleBlock_Data_Linear_96_96'])
        self.assertEqual(''.join(line+'\n' for _,source in split[:4]
            for line in source.splitlines() if line.startswith('def lc_')),literals)
        final=split[4][1]
        self.assertNotIn('def lc_',final)
        self.assertIn('def modulus : Nat := 7\n\ndef rawRoundRows :',final)
        self.assertEqual(final[final.index('def rawRoundRows'):],
                         regular[0][1][regular[0][1].index('def rawRoundRows'):])
        self.assertTrue(all('theorem ' not in source for _,source in split[:5]))
        for size in (True,0,65):
            with self.assertRaises(ValueError):split_block_data(regular[0][1],'ExampleBlock_Data',size)
        for malformed in (regular[0][1].replace('lc_3 :','lc_4 :'),original,
                          regular[0][1].replace('def lc_4 :','-- boundary\ndef lc_4 :')):
            with self.assertRaises(ValueError):split_block_data(malformed,'ExampleBlock_Data')


if __name__=='__main__':unittest.main()
