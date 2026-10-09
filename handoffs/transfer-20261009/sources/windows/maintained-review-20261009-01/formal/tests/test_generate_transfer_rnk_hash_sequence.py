"""Source-parser/render fixtures; no actual observation or Lean proof credit."""
import re
import unittest
from circuits import generate_transfer_rnk_hash_sequence as generator
from circuits.transfer_relation import RelationError


class RnkHashSequenceTests(unittest.TestCase):
    def fixture(self):
        sources = {}
        for block, (lower, upper) in enumerate([(60778,61193),(61194,61613),(61614,61929)]):
            stem = f'RuntimeTransferRnkHash{block}OwnedCompletion'; chunks = []
            for index in range(13):
                name = stem+f'Chunk{index}'; chunks.append(name)
                begin = lower+(upper-lower+1)*index//13
                end = lower+(upper-lower+1)*(index+1)//13
                sources[name] = (f'namespace ShielddSecurity.{name}\n'
                    f'def ownedWrites : List Nat := {list(range(begin,end))}\n'
                    f'def rawRows : List Row := [\n  ⟨[({begin}, (1 : Int))], []⟩]\n'
                    'def priorRows : List Row := []\n'+f'end ShielddSecurity.{name}\n').encode()
            sources[stem] = (f'import ShielddSecurity.RuntimeRnkHash{block}_Data\n'+
                ''.join('import ShielddSecurity.'+name+'\n' for name in chunks)+
                f'namespace ShielddSecurity.{stem}\n'+
                'theorem preserves : True := True.intro\n'
                'theorem complete_rows : True := True.intro\n'+
                f'end ShielddSecurity.{stem}\n').encode()
        return sources

    def test_complete_finite_write_ranges_and_three_audits(self):
        parts = generator.inspect_sources(self.fixture())
        self.assertEqual([(part['lower'],part['upper']) for part in parts],
            [(60778,61193),(61194,61613),(61614,61929)])
        name, source = generator.generate(self.fixture())
        self.assertEqual(name, 'RuntimeRnkHashSequenceCompletion')
        checks = re.findall(r'^#check @([^\s]+)',source,re.M)
        self.assertEqual(checks, re.findall(r'^#print axioms ([^\s]+)',source,re.M))
        self.assertEqual(len(checks),3)
        self.assertNotRegex(source,r'\((?:satisfied|constructed|desired)\s*:')
        self.assertIn('complete_rows base linked',source)
        self.assertTrue(source.startswith('import ShielddSecurity.Scalar\n'))
        self.assertIn('change row ∈ (',source)
        self.assertIn('rcases List.mem_append.mp member',source)
        self.assertNotIn('.priorRows,',source)

    def test_missing_source_or_wrong_import_refused(self):
        sources = self.fixture(); sources.pop('RuntimeTransferRnkHash0OwnedCompletionChunk0')
        with self.assertRaises(RelationError): generator.generate(sources)
        sources = self.fixture(); name = 'RuntimeTransferRnkHash0OwnedCompletion'
        sources[name] = sources[name].replace(b'RuntimeRnkHash0_Data',b'RuntimeRnkHash1_Data')
        with self.assertRaises(RelationError): generator.generate(sources)

    def test_write_collision_and_prior_support_refused(self):
        name = 'RuntimeTransferRnkHash0OwnedCompletionChunk1'
        sources = self.fixture()
        sources[name] = sources[name].replace(b'60810',b'60778')
        with self.assertRaises(RelationError): generator.generate(sources)
        sources = self.fixture()
        sources[name] = sources[name].replace(b'(60810, (1 : Int))',b'(61614, (1 : Int))')
        with self.assertRaises(RelationError): generator.generate(sources)

    def test_typed_malformed_source_refused(self):
        sources = self.fixture(); sources['RuntimeTransferRnkHash0OwnedCompletionChunk0'] = None
        with self.assertRaises(RelationError): generator.generate(sources)
        sources = self.fixture()
        sources['RuntimeTransferRnkHash0OwnedCompletionChunk0'] = sources[
            'RuntimeTransferRnkHash0OwnedCompletionChunk0'].replace(b'60778',b'True',1)
        with self.assertRaises(RelationError): generator.generate(sources)


if __name__ == '__main__': unittest.main()
