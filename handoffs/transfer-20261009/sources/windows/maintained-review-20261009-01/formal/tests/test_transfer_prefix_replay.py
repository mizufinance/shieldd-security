"""Unqualified stream/row controls, independent of source role acceptance."""
import copy,io,unittest
from unittest.mock import patch
from circuits import transfer_prefix_replay as prefix,transfer_relation as relation
from tests.test_transfer_relation import TransferRelationTests


class PrefixReplayTests(unittest.TestCase):
    def setUp(self):
        self.fixture=TransferRelationTests();self.fixture.setUp()

    def replay(self,parts,raw=None):
        return prefix.replay_rows(parts,io.BytesIO(self.fixture.encoded() if raw is None else raw),
            self.fixture.digest,4,1)

    def test_shared_rows_compared_once_with_complete_stream(self):
        parts=[('ivk',[self.fixture.row]),('reduction',[copy.deepcopy(self.fixture.row)])]
        with patch.object(relation,'inspect',wraps=relation.inspect) as stream:
            receipt=self.replay(parts)
        self.assertEqual(stream.call_count,1)
        self.assertEqual(receipt['rows'],1)
        self.assertEqual(receipt['row_uses'],{'0':['ivk','reduction']})

    def test_changed_retained_row_refuses_even_with_same_identity(self):
        row=copy.deepcopy(self.fixture.row);row['a'][1][1]=f'{3:064x}'
        with self.assertRaisesRegex(relation.RelationError,'original row mismatch'):
            self.replay([('ivk',[row])])

    def test_conflicting_alias_and_untyped_physical_index_refuse(self):
        row=copy.deepcopy(self.fixture.row);row['a'][1][1]=f'{3:064x}'
        with self.assertRaisesRegex(relation.RelationError,'conflicting'):
            self.replay([('ivk',[row]),('reduction',[self.fixture.row])])
        for index in (False,0.0,1):
            row=copy.deepcopy(self.fixture.row);row['row']=index
            with self.subTest(index=index),self.assertRaises(relation.RelationError):
                self.replay([('ivk',[row])])

    def test_truncation_and_late_extra_bytes_refuse(self):
        for raw in (self.fixture.encoded()[:-1],self.fixture.encoded()+b'{}\n'):
            with self.assertRaises(relation.RelationError):self.replay([('ivk',[self.fixture.row])],raw)


if __name__=='__main__':unittest.main()
