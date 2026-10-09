"""Exact column reuse accepts a real suffix shape and refuses folded prefixes."""
import copy,tempfile,unittest
from pathlib import Path
from circuits import generate_note_hash_block_completion as blocks
from circuits import generate_note_hash_completion as rounds,transfer_note_hash_renaming as renaming
from circuits import transfer_relation as relation
from tests.note_tree_path_fixture import path_fixture
from tests.test_note_hash_block_completion import native_rounds


class NoteHashRenamingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory=tempfile.TemporaryDirectory();cls.root=Path(cls.directory.name)
        cls.fixture=path_fixture(cls.root)
        f=cls.fixture
        cls.contexts=[blocks._context(f['pages'][i].read_bytes(),f['hashes'][i],f['note'],f['caller'],cls.root)
                      for i in (0,1)]
    @classmethod
    def tearDownClass(cls):cls.directory.cleanup()

    def test_suffix_constructs_actual_rows_and_preserves_every_other_column(self):
        plan=renaming._from_contexts(*self.contexts,2,65)
        columns=dict(plan['columns']);inverse={actual:source for source,actual in plan['columns']}
        self.assertEqual(len(columns),len(inverse))
        self.assertEqual([columns[c] for c in plan['source_writes']],plan['actual_writes'])
        p=relation.MODULUS;domain=self.contexts[1][1]['metadata']['domain_size']
        base={c:(37*c+19)%p for c in range(domain)}
        base[0]=base[self.contexts[1][1]['metadata']['constant_copy']]=1
        constructed={c:base[target] for c,target in plan['columns']}
        evaluate=lambda terms:sum(constructed[c]*v for c,v in terms)%p
        for index in range(2,65):
            for step in rounds._from_checked(*self.contexts[0],index)['steps']:
                left=evaluate(step['left']);remainder=evaluate(step['remainder'])
                if step['kind']=='square':value=left*left
                else:
                    right=evaluate(step['right']);value=left*right
                    constructed[step['auxiliary']]=(left-right)**2%p
                constructed[step['output']]=(value-remainder)%p
        actual=dict(base)
        for column in plan['actual_writes']:actual[column]=constructed[inverse[column]]
        evaluate_actual=lambda terms:sum(actual[c]*v for c,v in terms)%p
        self.assertTrue(all(evaluate_actual(a)**2%p==evaluate_actual(b) for a,b in plan['actual_rows'].values()))
        self.assertTrue(all(actual[c]==base[c] for c in range(domain) if c not in plan['actual_writes']))
        artifact=relation.record((self.root/'poseidon381-wide.json').read_bytes())
        initial=[sum(base[c]*v for c,v in terms)%p for terms in plan['actual_before']]
        self.assertEqual([evaluate_actual(terms) for terms in plan['actual_after']],
                         native_rounds(initial,artifact,2,65))
        actual[plan['actual_writes'][-1]]=(actual[plan['actual_writes'][-1]]+1)%p
        self.assertFalse(all(evaluate_actual(a)**2%p==evaluate_actual(b) for a,b in plan['actual_rows'].values()))

    def test_folded_prefix_coefficient_parameter_and_alias_changes_refused(self):
        with self.assertRaisesRegex(relation.RelationError,'LC coefficients/shape'):
            renaming._from_contexts(*self.contexts,0,65)
        changed=copy.deepcopy(self.contexts[1])
        changed[0]['calls'][0]['parameters']['mds'][0][0]+=1
        with self.assertRaisesRegex(relation.RelationError,'parameters differ'):
            renaming._from_contexts(self.contexts[0],changed,2,65)
        changed=copy.deepcopy(self.contexts[1])
        terms=list(changed[0]['calls'][0]['segments'][2]['before'][0]);c,v=terms[0]
        terms[0]=(c,(v+1)%relation.MODULUS)
        changed[0]['calls'][0]['segments'][2]['before'][0]=tuple(terms)
        with self.assertRaises(relation.RelationError):
            renaming._from_contexts(self.contexts[0],changed,2,65)

    def test_generated_chunk_requires_exact_rows_inverse_and_interfaces(self):
        f=self.fixture
        name,source=renaming.generate_chunk(f['pages'][0].read_bytes(),f['hashes'][0],
            f['pages'][1].read_bytes(),f['hashes'][1],f['note'],f['caller'],self.root,1)
        self.assertEqual(name,'RuntimeNoteHash0State1RenamedCompletionChunk1')
        self.assertEqual(source.count('#print axioms'),10)
        self.assertIn('RowCompletionRenaming.complete_rows',source)
        self.assertIn('rawRows = RuntimeNoteHash0State0CompletionChunk1.rawRows.map',source)
        self.assertIn('inverse_rows_checked',source)
        self.assertIn('inverse_writes_checked',source)
        self.assertIn('inverse_interface_checked',source)
        self.assertIn('interface_checked',source)
        signature=source[source.index('theorem complete_rows'):source.index(' := by',source.index('theorem complete_rows'))]
        self.assertNotIn('(satisfied :',signature)
        self.assertNotIn('(completed :',signature)
        with self.assertRaisesRegex(relation.RelationError,'folded prefix'):
            renaming.generate_chunk(f['pages'][0].read_bytes(),f['hashes'][0],
                f['pages'][1].read_bytes(),f['hashes'][1],f['note'],f['caller'],self.root,0)

    def test_generated_native_soundness_uses_actual_parameters_and_all_coordinate_links(self):
        f=self.fixture
        for chunk in (1,12):
            name,source=renaming.generate_sound_chunk(f['pages'][0].read_bytes(),f['hashes'][0],
                f['pages'][1].read_bytes(),f['hashes'][1],f['note'],f['caller'],self.root,chunk)
            self.assertEqual(name,f'RuntimeNoteHash0State1RenamedSoundChunk{chunk}')
            self.assertEqual(source.count('#print axioms'),16)
            self.assertEqual(source.count('Poseidon.round_certificate_sound'),5)
            self.assertIn('theorem parameters_checked : parameters =',source)
            self.assertIn('Compiler.unoutline_rows_sound pulled 32000',source)
            for index in range(5*chunk,5*chunk+5):
                signature=source[source.index(f'theorem round_sound_{index}'):
                    source.index(' := by',source.index(f'theorem round_sound_{index}'))]
                self.assertIn(f'Satisfies rho rawRows{index}',signature)
                self.assertNotIn('completed',signature)
                self.assertNotIn('sourceSatisfied',signature)
                self.assertIn(f'interface_checked_{index} : ∀ coordinate : Fin 6',source)
            # A valid construction really satisfies the transported rows. Native
            # coordinates are compared independently, including all six lanes.
            plan=renaming._from_contexts(*self.contexts,5*chunk,5*chunk+5)
            p=relation.MODULUS;columns=dict(plan['columns'])
            rho={c:(23*c+11)%p for c in columns.values()}
            rho[0]=rho[32000]=1
            initial=[sum(rho[columns[c]]*v for c,v in lc)%p for lc in plan['source_before']]
            constructed={c:rho[target] for c,target in plan['columns']}
            evaluate=lambda lc:sum(constructed[c]*v for c,v in lc)%p
            for index in range(5*chunk,5*chunk+5):
                for step in rounds._from_checked(*self.contexts[0],index)['steps']:
                    left=evaluate(step['left']);remainder=evaluate(step['remainder'])
                    if step['kind']=='square':value=left*left
                    else:
                        right=evaluate(step['right']);value=left*right
                        constructed[step['auxiliary']]=(left-right)**2%p
                    constructed[step['output']]=(value-remainder)%p
            artifact=relation.record((self.root/'poseidon381-wide.json').read_bytes())
            self.assertEqual([evaluate(lc) for lc in plan['source_after']],
                native_rounds(initial,artifact,5*chunk,5*chunk+5))
        with self.assertRaisesRegex(relation.RelationError,'folded prefix'):
            renaming.generate_sound_chunk(f['pages'][0].read_bytes(),f['hashes'][0],
                f['pages'][1].read_bytes(),f['hashes'][1],f['note'],f['caller'],self.root,0)

    def test_prior_actual_row_support_preserved(self):
        f=self.fixture
        for index in (1,12):
            name,source=renaming.generate_preservation(f['pages'][0].read_bytes(),f['hashes'][0],
                f['pages'][1].read_bytes(),f['hashes'][1],f['note'],f['caller'],self.root,index)
            self.assertEqual(name,f'RuntimeNoteHash0State1RenamedCompletionStage{index}')
            self.assertEqual(source.count('#print axioms'),5)
            self.assertIn('ColumnFence.checked_rows',source)
            self.assertNotIn('term.1 ∉ ownedWrites))) = true := by decide',source)
            plan=renaming._from_contexts(*self.contexts,5*index,5*index+5)
            writes=set(plan['actual_writes'])
            earlier={row for segment in self.contexts[1][0]['calls'][0]['segments'][:5*index]
                     for row in segment['rows']}
            self.assertTrue(all(c not in writes for row in earlier
                for terms in self.contexts[1][0]['rows'][row] for c,_ in terms))
            # Even a syntactically nonlinear earlier row is unchanged for any
            # base assignment and arbitrary values of newly owned columns.
            base=lambda c:(41*c+5)%relation.MODULUS
            changed=lambda c:17 if c in writes else base(c)
            evaluate=lambda rho,lc:sum(rho(c)*v for c,v in lc)%relation.MODULUS
            for row in earlier:
                for lc in self.contexts[1][0]['rows'][row]:
                    self.assertEqual(evaluate(base,lc),evaluate(changed,lc))


if __name__=='__main__':unittest.main()
