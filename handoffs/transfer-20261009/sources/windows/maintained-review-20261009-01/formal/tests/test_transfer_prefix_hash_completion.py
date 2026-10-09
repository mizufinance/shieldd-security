"""Unqualified arithmetic fixtures; no runtime/source parameter qualification."""
import copy,json,unittest
from circuits import generate_transfer_prefix_hash_completion as completion,transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine


def fixture(width):
    rows={};segments=[];state=[((3+i,1),) for i in range(width)];pivot=100
    outline=lambda lc:canonical((5000 if c==0 else c,v) for c,v in lc)
    def add(a,b):
        index=len(rows);rows[index]=(outline(a),outline(b));return index
    for index in range(65):
        before=copy.deepcopy(state);fifths={};indices=[]
        for lane in (range(width) if index<4 or index>=61 else (0,)):
            base=state[lane];square=((pivot,1),);fourth=((pivot+1,1),);output=((pivot+2,1),);aux=((pivot+3,1),);pivot+=4
            ids=[add(base,square),add(square,fourth),add(combine(fourth,base,-1),aux),add(combine(fourth,base),combine(aux,output,4))]
            fifths[lane]=dict(kind='arithmetic',square=square,fourth=fourth,auxiliary=aux,rows=ids)
            state[lane]=output;indices.extend(ids)
        segments.append(dict(kind='round',chunk=0,index=index,before=before,shifted=before,
            transformed=copy.deepcopy(state),after=copy.deepcopy(state),fifths=fifths,rows=indices))
    link=add(((0,1),(5000,relation.MODULUS-1)),())
    # add outlines constants; retain the actual global0/copy linkage instead.
    rows[link]=(canonical([(0,1),(5000,-1)]),())
    parameters=dict(width=width,ark=[[0]*width for _ in range(65)],
        mds=[[int(i==j) for j in range(width)] for i in range(width)])
    selected=dict(outline=5000,constant_link=link,rows=rows,calls=[dict(role='diagnostic',parameters=parameters,segments=segments)])
    return selected,dict(domain_size=8192,constant_copy=5000)


class PrefixHashCompletionTests(unittest.TestCase):
    def test_width3_and6_same_bounded_arithmetic_constructor(self):
        for width in (3,6):
            selected,metadata=fixture(width)
            # Persisted RNK recurrence stores LC arrays. Lane keys are restored
            # by its typed parser; this fixture exercises LC roundtrip handling.
            for segment in selected['calls'][0]['segments']:
                for key in ('before','shifted','transformed','after'):
                    segment[key]=json.loads(json.dumps(segment[key]))
            plans=[]
            modules=list(completion._emit(selected,metadata,'DiagnosticPrefix','DiagnosticData','DiagnosticSound',
                [((3+i,1),) for i in range(width)],lambda index,plan:plans.append(plan)))
            self.assertEqual(len(modules),14);self.assertEqual(len(plans),13)
            self.assertTrue(all(plan['stop']-plan['start']<=5 for plan in plans))
            self.assertEqual({i for plan in plans for i in plan['raw']},set(selected['rows']))
            self.assertTrue(all('sorry' not in source for _,source in modules))
            for _,source in modules[:-1]:
                self.assertEqual(source.count('#check @'),10)
                signature=source[source.index('theorem complete '):source.index(' :=',source.index('theorem complete '))]
                self.assertNotIn('satisfied',signature)
            self.assertEqual(modules[-1][1].count('#check @'),3)

    def test_actual_write_alias_and_malformed_readonly_refused(self):
        selected,metadata=fixture(3)
        for readonly in ([((100,1),)],[((3,True),)],[((4,1),(3,1))]):
            with self.assertRaises(relation.RelationError):
                list(completion._emit(selected,metadata,'DiagnosticPrefix','DiagnosticData','DiagnosticSound',readonly))

    def test_derivative_shift_mds_and_untransformed_lane_changes_refuse(self):
        for key,index,lane in (('shifted',0,0),('after',0,0),('transformed',5,1)):
            selected,metadata=fixture(3)
            segment=selected['calls'][0]['segments'][index]
            segment[key]=copy.deepcopy(segment[key])
            segment[key][lane]=((3,7),)
            with self.subTest(key=key),self.assertRaises(relation.RelationError):
                completion.validate_selected(selected,metadata)


if __name__=='__main__':unittest.main()
