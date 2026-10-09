"""Tiny byte lifecycle/physical projection fixtures, never qualified captures."""
import io,json,unittest
from circuits import transfer_balance_joint_rows as joint,transfer_relation as relation


def encoded(value):return (json.dumps(value,separators=(',',':'))+'\n').encode()


class JointBalanceRowsTests(unittest.TestCase):
    def test_forwarded_bytes_and_exact_eof_lifecycle(self):
        rows=[dict(row=0,a=[],b=[]),dict(row=1,a=[[3,f'{1:064x}']],b=[])]
        lines=[encoded(dict(schema='shieldd-transfer-relation-v1')),*map(encoded,rows),encoded(dict(eof=True,rows=2))]
        observed=[];tap=joint._RowTap(io.BytesIO(b''.join(lines)),observed.append)
        self.assertEqual([tap.readline() for _ in lines],lines)
        self.assertEqual(observed,rows);self.assertEqual(tap.read(1),b'')
        self.assertTrue(tap.eof and tap.tail)
        with self.assertRaises(relation.RelationError):tap.readline()
        with self.assertRaises(relation.RelationError):tap.read(1)
        bad=joint._RowTap(io.BytesIO(lines[0]+encoded(dict(row=1,a=[],b=[]))),lambda _:None)
        bad.readline()
        with self.assertRaises(relation.RelationError):bad.readline()

    def test_shared_physical_rows_project_without_copying_flags_or_roles(self):
        rows=[dict(row=i,a=[],b=[]) for i in (2,4,6)]
        combined=dict(identity={'raw_sha256':'fixture-only'},templates=[
            dict(row=2,roles=['variable.page.0.constant-copy','blinding.page.0.constant-copy'])],
            products=[dict(role='variable.page.0.product',rows=[4]),dict(role='blinding.page.0.product',rows=[6])],
            selected_rows=rows)
        v=joint._project(combined,'variable.');b=joint._project(combined,'blinding.')
        self.assertEqual(v['selected_rows'],rows[:2]);self.assertEqual(b['selected_rows'],[rows[0],rows[2]])
        self.assertEqual(v['templates'][0]['roles'],['page.0.constant-copy'])
        self.assertIs(v['selected_rows'][0],b['selected_rows'][0])
        self.assertNotIn('ordinary_full_ordered_rows_equal',v)
        for altered in (dict(combined,selected_rows=rows[1:]),dict(combined,selected_rows=rows[::-1])):
            with self.assertRaises(relation.RelationError):joint._project(altered,'blinding.')
        with self.assertRaises(relation.RelationError):joint._project(combined,'epk.')

    def test_actual_parent_refusal_precedes_any_stream_read(self):
        class Unopened:
            def readline(self):raise AssertionError('unqualified stream touched')
        with self.assertRaises(relation.RelationError):
            joint.extract_rows(Unopened(),b'{}\n',[],b'{}\n',[],b'{}\n',b'{}\n',{}, {},[],[])
