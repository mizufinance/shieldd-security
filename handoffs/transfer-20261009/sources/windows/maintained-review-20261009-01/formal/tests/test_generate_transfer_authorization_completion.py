"""Typed source fixtures only; no capture or proof qualification."""
import unittest
from circuits.generate_transfer_authorization_completion import generate_fixed_coverage,FIXED_STARTS
from circuits.transfer_relation import RelationError


def fixture():
    def module(name,body):return ('namespace ShielddSecurity.'+name+'\n'+body+
        'end ShielddSecurity.'+name+'\n').encode()
    sources={}
    for index in range(126):
        name=f'RuntimeFixedSpendWindow{index:03d}'
        sources[name]=module(name,'def rawRows : List Row := []\n')
    chunks=[]
    for start in FIXED_STARTS:
        name=f'RuntimeFixedSpendChunk{start:03d}';chunks.append(name)
        blocks=[f'ShielddSecurity.RuntimeFixedSpendWindow{index:03d}.rawRows' for index in range(start,min(start+16,126))]
        sources[name]=module(name,'def blocks : List (List Row) := ['+','.join(blocks)+']\n'+
            'def rawRows : List Row := blocks.flatten\n')
    name='RuntimeTransferRandomizer';blocks=[f'c{index}Raw' for index in range(16)]+['tailRaw']
    sources[name]=module(name,''.join('def '+block+' : List Row := []\n' for block in blocks)+
        'def originalBlocks : List (List Row) := ['+', '.join(blocks)+']\n'+
        'def originalRows : List Row := originalBlocks.flatten\n')
    name='RuntimeTransferFixedSpend'
    blocks=['ShielddSecurity.'+chunk+'.rawRows' for chunk in chunks]+['ShielddSecurity.RuntimeTransferRandomizer.originalRows']
    sources[name]=module(name,'def blocks : List (List Row) := ['+','.join(blocks)+']\n'+
        'def rawRows : List Row := blocks.flatten\n')
    return sources


class AuthorizationCompletionSourceTests(unittest.TestCase):
    def test_ten_bounded_candidates_and_symbolic_whole_join(self):
        modules=generate_fixed_coverage(fixture())
        self.assertEqual(len(modules),10)
        for name,source in modules.items():
            self.assertEqual(source.count('#check @'),1)
            self.assertNotIn('Satisfies',source)
            self.assertNotRegex(source,r'\b(sorry|admit|axiom)\b')
            self.assertLessEqual(source.count('private theorem block'),17)
        whole=modules['RuntimeTransferFixedSpend_Frame']
        self.assertNotIn('by decide',whole)
        self.assertIn('RuntimeTransferRandomizer_Frame.rows_covered',whole)

    def test_missing_duplicate_or_reordered_source_refuses(self):
        sources=fixture();sources.pop('RuntimeFixedSpendWindow125')
        with self.assertRaises(RelationError):generate_fixed_coverage(sources)
        for old,new in ((b'Window000.rawRows',b'Window001.rawRows'),(b'Window015.rawRows',b'Window014.rawRows')):
            sources=fixture();key='RuntimeFixedSpendChunk000';sources[key]=sources[key].replace(old,new)
            with self.assertRaises(RelationError):generate_fixed_coverage(sources)

    def test_original_tail_and_unclosed_namespace_refuse(self):
        for key,old,new in (('RuntimeTransferRandomizer',b'def tailRaw',b'def otherRaw'),
                ('RuntimeFixedSpendWindow125',b'end ShielddSecurity.RuntimeFixedSpendWindow125',b'')):
            sources=fixture();sources[key]=sources[key].replace(old,new)
            with self.assertRaises(RelationError):generate_fixed_coverage(sources)


if __name__=='__main__':unittest.main()
