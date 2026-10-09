"""Unqualified typed declarations test bounded source selection/refusal only."""
import unittest
from circuits.generate_transfer_prefix_frames import generate,_pair
from circuits.transfer_relation import RelationError


def fixture():
    def module(name,body):return ('namespace ShielddSecurity.'+name+'\n'+body+
        'end ShielddSecurity.'+name+'\n').encode()
    sources={}
    for index in range(126):
        name=f'RuntimeFixedSpendWindow{index:03d}Program'
        sources[name]=module(name,'def program (low high : Bool) : GroupFixedCircuitCompletion.Program where\n'+
            f'  stages := ShielddSecurity.RuntimeFixedSpendWindow{index:03d}Completion.completionSteps\n')
    name='RuntimeTransferFixedSpendCompletion'
    sources[name]=module(name,'def segments (n : Nat) : List (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame) := ['+
        ','.join(_pair(index) for index in range(126))+']\n')
    name='RuntimeFixedSpendRandomizerOrder'
    sources[name]=module(name,'def prefix000 : List CompilerCompletion.Step := []\n'+
        ''.join(f'def chunk{index:03d} : List CompilerCompletion.Step := []\n'+
            f'def prefix{index+1:03d} : List CompilerCompletion.Step := prefix{index:03d} ++ chunk{index:03d}\n'
            for index in range(16))+'def allStages : List CompilerCompletion.Step := prefix016\n')
    return sources


class PrefixFrameSourceTests(unittest.TestCase):
    def test_bounded_checks_and_symbolic_lower_origin(self):
        modules=generate(fixture())
        self.assertEqual(len(modules),10)
        for source in modules.values():
            self.assertEqual(source.count('#check @'),1)
            self.assertNotIn('Satisfies',source)
            self.assertNotRegex(source,r'\b(sorry|admit|axiom)\b')
            self.assertLessEqual(source.count('private theorem gap'),16)
        self.assertIn('GroupPrefixFrameTransport.lower_origin_certified',modules['RuntimeTransferFixedSpendPrefixFrames'])
        self.assertEqual(modules['RuntimeFixedSpendRandomizerPrefixWrites'].count('private theorem chunk'),16)

    def test_missing_or_reordered_allocation_refuses(self):
        sources=fixture();sources.pop('RuntimeFixedSpendWindow125Program')
        with self.assertRaises(RelationError):generate(sources)
        sources=fixture();key='RuntimeTransferFixedSpendCompletion'
        sources[key]=sources[key].replace(_pair(0).encode(),_pair(1).encode())
        with self.assertRaises(RelationError):generate(sources)

    def test_missing_comparator_or_changed_stage_source_refuses(self):
        for key,old,new in (('RuntimeFixedSpendRandomizerOrder',b'def chunk015',b'def otherChunk'),
                ('RuntimeFixedSpendWindow000Program',b'Window000Completion.completionSteps',b'Window001Completion.completionSteps')):
            sources=fixture();sources[key]=sources[key].replace(old,new)
            with self.assertRaises(RelationError):generate(sources)


if __name__=='__main__':unittest.main()
