"""Tiny typed source fixtures only; no runtime qualification or EPK theorem credit."""
import copy,json,unittest
from circuits import transfer_epk_fixed as epk,transfer_relation as relation

DIGEST='16e7b009b763be55ca21f423f4f97e8c132b40b6adbcd06f6a3be17f2d0ef236'
def encoded(o):return (json.dumps(o,separators=(',',':'))+'\n').encode()
def native(n):return {'native':f'{n%relation.MODULUS:064x}'}
def source(n):return {'source':[1,n]}
def fixture():
    identity=[native(0),native(1)];bits=[[1,i] for i in range(10,262)]
    randomizer=source(0);published=[source(402),source(403)];output=[source(400),source(401)];inverse=source(404)
    common=dict(relation_digest=DIGEST,domain_size=262144,full_rows=200770,constant_copy=200692,
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True)
    entry=dict(randomizer=randomizer,bits=bits,capsule=published+[source(450+i) for i in range(5)],computed_epk=output,epk_inverse=inverse)
    roots=set(map(tuple,bits))|{(1,n) for n in [0,400,401,402,403,404]}
    observed={h:((h[1]+3,1),) for h in roots}
    expressions=[dict(source=list(h),terms=[[h[1]+3,f'{1:064x}']]) for h in sorted(roots)]
    capsules=dict(metadata=dict(common,schema='shieldd-transfer-recovery-capsule-roles-v1',capsules=[entry,entry]),observed=observed,metadata_sha256='a'*64)
    caller=dict(metadata=dict(common,spend={'generator':identity}),observed={},metadata_sha256='b'*64)
    obj=dict(common,schema='shieldd-transfer-epk-fixed-v1',family='transfer',scope=epk.SCOPE,lane='recovery',slot=0,
        window_start=0,window_count=1,total_windows=126,bit_width=252,base=identity,randomizer=randomizer,inverse=inverse,bits=bits,
        published=published,output=output,expressions=expressions,nodes=[],windows=[dict(index=0,table=[identity]*4,
            points=[identity]*3,bits=bits[:2],arithmetic=[native(0),native(1),native(1),native(0)],
            quotient=[native(0),native(1),native(1),native(1),native(0),native(1)])])
    return obj,capsules,caller
class EpkFixedIngressTests(unittest.TestCase):
    def test_typed_roles_generate_only_original_row_obligations(self):
        obj,capsules,caller=fixture();checked=epk.inspect_recovery_page(encoded(obj),capsules,caller)
        self.assertEqual(len(checked['products']),6);self.assertEqual(len(checked['quotients']),2)
        self.assertIn('original rows',checked['scope']);self.assertIsNone(checked['qualification_parent_sha256'])
    def test_semantic_native_table_and_quotient_substitution_refusal(self):
        for path in ['table','quotient','bits','inverse','base','randomizer']:
            obj,capsules,caller=fixture()
            if path=='table':obj['windows'][0]['table'][1]=[native(2),native(1)]
            elif path=='quotient':obj['windows'][0]['quotient'][0]=native(1)
            elif path=='bits':obj['windows'][0]['bits'].reverse()
            elif path=='base':obj['base']=[native(0),native(-1)]
            else:obj[path]=source(999)
            with self.subTest(path=path),self.assertRaises(relation.RelationError):epk.inspect_recovery_page(encoded(obj),capsules,caller)
    def test_full_original_identity_and_parent_shared_lc_refusal(self):
        for edit in ['digest','pending','parent','lc','missing','schema']:
            obj,capsules,caller=fixture()
            if edit=='digest':obj['relation_digest']='c'*64;capsules['metadata']['relation_digest']='c'*64;caller['metadata']['relation_digest']='c'*64
            elif edit=='pending':obj['ordinary_full_ordered_rows_equal']=False
            elif edit=='parent':capsules['metadata']['repeated_observations_equal']=False
            elif edit=='lc':capsules['observed'][(1,10)]=((13,2),)
            elif edit=='missing':obj['expressions'].pop()
            else:obj['schema']='shieldd-transfer-fixed-spend-v1'
            with self.subTest(edit=edit),self.assertRaises(relation.RelationError):epk.inspect_recovery_page(encoded(obj),capsules,caller)
    def test_derivative_view_retains_pending_false_bytes(self):
        obj,capsules,caller=fixture();obj['ordinary_full_ordered_rows_equal']=False;obj['repeated_observations_equal']=False
        data=encoded(obj);checked=epk._inspect_recovery_page(data,capsules,caller,qualification_parent_sha256='d'*64)
        self.assertIs(checked['metadata']['ordinary_full_ordered_rows_equal'],False)
        self.assertEqual(checked['metadata_sha256'],__import__('hashlib').sha256(data).hexdigest())

    def test_public_derivative_entry_requires_real_complete_parent(self):
        obj,capsules,caller=fixture()
        for parent,pages in [(b"{}\n",[]),(encoded(dict(schema='shieldd-transfer-epk-fixed-pages-v1')), [encoded(obj)]*8)]:
            with self.assertRaises(relation.RelationError):epk.inspect_recovery_pages(parent,pages,capsules,caller)
