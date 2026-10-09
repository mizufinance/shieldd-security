"""Synthetic source/row refusals only; no production qualification or proof credit."""
import copy,hashlib,json,unittest
import blake3
from circuits import transfer_balance_blinding_fixed as ingress,transfer_balance_blinding_completion as completion
from circuits import transfer_balance_blinding_batch as batch,transfer_relation as relation


def encoded(obj):return (json.dumps(obj,separators=(',',':'))+'\n').encode()
def native(n):return {'native':f'{n%relation.MODULUS:064x}'}


def fixture():
    # Native identity is deliberately a tiny folded table fixture, not the
    # production VALUE_BLINDING parameter. Expected native object is explicit.
    identity=[native(0),native(1)];bits=[[1,i] for i in range(10,262)];scalar={'source':[1,0]}
    common=dict(relation_digest=ingress.DIGEST,domain_size=262144,full_rows=200770,constant_copy=200692)
    expressions=[dict(source=h,terms=[[h[1]+3,f'{1:064x}']]) for h in [[1,0],*bits]]
    raw=[];descriptors=[]
    for ordinal in range(8):
        start=16*ordinal;count=min(16,126-start)
        obj=dict(common,schema='shieldd-transfer-balance-blinding-fixed-v1',family='transfer',scope=ingress.SCOPE,generator='VALUE_BLINDING',
            ordinary_full_ordered_rows_equal=False,repeated_observations_equal=False,
            window_start=start,window_count=count,total_windows=126,bit_width=252,base=identity,blinding=scalar,bits=bits,output=identity,
            windows=[dict(index=i,table=[identity]*4,points=[identity]*3,bits=bits[2*i:2*i+2],
                arithmetic=[native(0),native(1),native(1),native(0)],quotient=[native(0),native(1),native(1),native(1),native(0),native(1)])
                for i in range(start,start+count)],expressions=expressions,nodes=[])
        data=encoded(obj);raw.append(data);descriptors.append(dict(ordinal=ordinal,window_start=start,window_count=count,blake3=blake3.blake3(data).hexdigest()))
    parent=dict(common,schema='shieldd-transfer-balance-blinding-fixed-pages-v1',family='transfer',scope=ingress.PARENT_SCOPE,generator='VALUE_BLINDING',
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,pages=descriptors)
    return parent,raw,identity,scalar


class BlindingIngressTests(unittest.TestCase):
    def test_genuine_schema_retains_false_raw_identity_and_zero_bit_assignment(self):
        parent,raw,base,scalar=fixture();checked=ingress.inspect_pages(encoded(parent),raw,base,scalar)
        self.assertEqual(sum(len(c['points']) for c in checked['chunks']),126)
        self.assertEqual(checked['parent_sha256'],hashlib.sha256(encoded(parent)).hexdigest())
        self.assertTrue(all(c['metadata']['ordinary_full_ordered_rows_equal']is False for c in checked['chunks']))
        page=checked['chunks'][0];required,products,squares=completion.requirements(page)
        self.assertEqual((products,squares),([],[]))
        extraction=dict(metadata_sha256=page['metadata_sha256'],include_canonical=False,
            identity={'relation_digest':ingress.DIGEST,'domain_size':262144,'stored_rows':200770},
            selected_rows=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in a],b=[[c,f'{v:064x}'] for c,v in b]) for i,(a,b) in enumerate(required)])
        plan=completion.completion_plan(page,extraction,readonly_lcs=(((6,1),),))
        self.assertEqual(plan['writes'],[]);self.assertTrue({0,1,2,3,6,200692}<=set(plan['kept']))
        # Explicit zero blinding and allzero bits satisfy these real-shaped
        # original Boolean/copy equations. Canonical/native/full balance OPEN.
        rho={0:1,200692:1,3:0}
        for row in extraction['selected_rows']:
            a,b=[sum(rho.get(c,0)*int(v,16) for c,v in row[key])%relation.MODULUS for key in ('a','b')]
            self.assertEqual(a*a%relation.MODULUS,b)
        with self.assertRaises(relation.RelationError):completion.completion_plan(page,dict(extraction,selected_rows=extraction['selected_rows'][:-1]))
        self.assertEqual(len(batch.requirements(checked)[0]),253)

    def test_rehashed_wrong_table_quotient_scope_parent_and_source_refuse(self):
        for change in ('table','quotient','bits','source','extra','epk','flag','shape','scalar','pagecount'):
            parent,raw,base,scalar=fixture();obj=json.loads(raw[1])
            if change=='table':obj['windows'][0]['table'][1]=[native(1),native(1)]
            elif change=='quotient':obj['windows'][0]['quotient'][0]=native(1)
            elif change=='bits':obj['windows'][0]['bits'].reverse()
            elif change=='source':obj['expressions'][0]['terms'][0][1]=f'{2:064x}'
            elif change=='extra':obj['inverse']={'source':[1,0]}
            elif change=='epk':obj['schema']='shieldd-transfer-epk-fixed-v1'
            elif change=='flag':obj['repeated_observations_equal']=True
            elif change=='shape':parent['full_rows']=200769
            elif change=='scalar':scalar={'source':[1,1]}
            else:raw.pop()
            if change!='pagecount':raw[1]=encoded(obj);parent['pages'][1]['blake3']=blake3.blake3(raw[1]).hexdigest()
            with self.subTest(change=change),self.assertRaises(relation.RelationError):ingress.inspect_pages(encoded(parent),raw,base,scalar)

    def test_parent_order_hash_and_flags_and_extra_ast_refuse(self):
        for change in ('ordinal','digest','flag','ast','expectedbase','duplicatebits'):
            parent,raw,base,scalar=fixture()
            if change=='ordinal':parent['pages'][7]['ordinal']=True
            elif change=='digest':parent['pages'][0]['blake3']='a'*64
            elif change=='flag':parent['ordinary_full_ordered_rows_equal']=False
            elif change=='expectedbase':base=[native(0),native(-1)]
            else:
                obj=json.loads(raw[0])
                if change=='ast':obj['nodes']=[dict(index=10,multiply=True,left=[1,10],right=[1,11])]
                else:obj['bits'][0]=obj['bits'][1]
                raw[0]=encoded(obj);parent['pages'][0]['blake3']=blake3.blake3(raw[0]).hexdigest()
            with self.subTest(change=change),self.assertRaises(relation.RelationError):ingress.inspect_pages(encoded(parent),raw,base,scalar)
