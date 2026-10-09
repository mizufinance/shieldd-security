"""Legacy equivalent Div-template controls; not the pinned authorization Point.add source."""
import copy
import io
import json
import unittest
from unittest.mock import patch
from circuits import transfer_rk_addition as addition, transfer_relation as relation
from circuits import transfer_authorization_roles as roles
from circuits.transfer_balance_rows import canonical, combine
from circuits.transfer_fixed_spend import D
from tests import test_transfer_rk_binding as rk_fixture


def fixture(change=None):
    rows=[]
    outline=lambda lc:canonical((1000 if c==0 else c,v) for c,v in lc)
    def row(a,b=()):rows.append(dict(row=len(rows),a=[[c,f'{v:064x}'] for c,v in canonical(a)],b=[[c,f'{v:064x}'] for c,v in canonical(b)]))
    def product(left,right,out,aux):
        row(outline(combine(left,right,-1)),[(aux,1)])
        row(outline(combine(left,right)),combine(((aux,1),),out,4))
    row([(0,1),(1000,-1)])
    xx,yy,summed,xy=[((c,1),) for c in (600,601,602,603)]
    product(((4,1),),((420,1),),xx,650)
    product(((5,1),),((421,1),),yy,651)
    product(((4,1),(5,1)),((420,1),(421,1)),summed,652)
    product(xx,yy,xy,653)
    ns=[combine(combine(summed,xx,-1),yy,-1),combine(yy,xx)]
    ds=[combine(((0,1),),((603,D),)),combine(((0,1),),((603,D),),-1)]
    for i in range(2):
        out=((610+i,1),);product(((422+i,1),),ds[i],out,660+i)
        row(outline(combine(out,ns[i],-1)))
    if change:change(rows)
    for i,record in enumerate(rows):record['row']=i
    data,stream,digest,handles,rnk,ivk=rk_fixture.fixture(rows=rows)
    accepted=roles.inspect_metadata(data,digest,handles,rnk,ivk)
    return data,accepted,stream.getvalue()


class RkAdditionTests(unittest.TestCase):
    def test_unique_actual_products_and_both_quotient_assertions(self):
        data,accepted,stream=fixture()
        extracted=addition._extract_legacy(data,accepted,lambda:io.BytesIO(stream))
        self.assertEqual(extracted['intermediates']['xy'],[[603,1]])
        self.assertEqual(len(extracted['selected_rows']),15)
        source=addition.generate(data,accepted,json.loads(json.dumps(extracted)))
        for name in ('actual_addition_rows','actual_add_coordinates','complete_quotient0','complete_quotient1'):
            self.assertIn('#check @'+name,source);self.assertIn('#print axioms '+name,source)
        self.assertNotIn('sorry',source);self.assertNotIn('native_decide',source)

    def test_missing_changed_assertion_and_ambiguous_producer_refuse(self):
        def missing(rows):rows.pop()
        def changed(rows):rows[-1]['a'][0][1]=f'{2:064x}'
        def ambiguous(rows):
            rows.append(copy.deepcopy(rows[1]));rows.append(copy.deepcopy(rows[2]))
        for change in (missing,changed,ambiguous):
            data,accepted,stream=fixture(change)
            with self.subTest(change=change.__name__),self.assertRaises(relation.RelationError):
                addition._extract_legacy(data,accepted,lambda:io.BytesIO(stream))

    def test_same_role_handle_changed_lc_and_persisted_product_refuse(self):
        data,accepted,stream=fixture();extracted=addition._extract_legacy(data,accepted,lambda:io.BytesIO(stream))
        changed=copy.deepcopy(accepted);changed['observed'][(2,20)]=((999,1),)
        with self.assertRaisesRegex(relation.RelationError,'shared source LCs'):
            addition._extract_legacy(data,changed,lambda:io.BytesIO(stream))
        extracted['intermediates']['xy']=[[604,1]]
        with self.assertRaises(relation.RelationError):addition.generate(data,accepted,extracted)

    def test_full_caller_signature_is_preserved_on_combined_rows(self):
        # The maintained renderer supplies the signature. Its component roles
        # are mocked here; this test makes no claim that those Lean equalities
        # hold for this unrelated small fixture.
        from circuits import transfer_authorization_join as caller
        data,accepted,stream=fixture();extracted=addition._extract_legacy(data,accepted,lambda:io.BytesIO(stream))
        obj=accepted['metadata'];observed=accepted['observed'];values={}
        def lc(ref):return observed[tuple(ref['source'])]
        for name in ('regulated','asset','nk','effective_nk','registered_rnk'):
            values[name]=lc(obj['caller'][name])
        for name in ('ak','address','rnk_dh','selected_ring','leaf_ring'):
            for i,ref in enumerate(obj['caller'][name]):values[name+str(i)]=lc(ref)
        for i,ref in enumerate(obj['caller']['fixed_ring']):values['fixed_ring'+str(i)]=canonical([(0,int(ref['native'],16))])
        for name in ('hash','commitment'):values[name]=lc(obj['rnk_bindings'][name])
        with patch.object(caller,'inspect_join',return_value=dict(metadata=obj,values=values)):
            caller_source=caller.generate_caller_join(accepted,{},[])
        source=addition.generate_spend_join(data,accepted,extracted,caller_source)
        self.assertIn('#check @actual_caller_with_spend_rows',source)
        self.assertIn('#print axioms actual_caller_with_spend_rows',source)
        self.assertIn('(satisfied : Satisfies rho RuntimeTransferSpendAuthorization.rawRows)',source)
        self.assertIn('exact actual_caller rho one four codec model standardOrder',source)
        for malformed in ('theorem something_else',7):
            with self.assertRaises(relation.RelationError):addition.generate_spend_join(data,accepted,extracted,malformed)


if __name__=='__main__':unittest.main()
