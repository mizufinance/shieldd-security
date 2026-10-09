"""Typed fixture ingress only; no real fixed capture or row proof is claimed."""
import copy
import unittest

from circuits import transfer_authorization_roles as roles, transfer_fixed_spend as fixed
from circuits import transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine
from circuits.transfer_canonical_balance import ORDER
from tests import test_transfer_authorization_roles as fixtures


def fixture():
    base = fixtures.AuthorizationRoleTests(); base.setUp()
    accepted = roles.inspect_metadata(fixtures.encoded(base.obj), base.obj['relation_digest'],
                                     base.obj['ivk_handles'], base.rnk, base.ivk)
    obj = {key: copy.deepcopy(base.obj[key]) for key in
           ('family','relation_digest','domain_size','full_rows','constant_copy','ordinary_full_ordered_rows_equal')}
    spend = base.obj['spend']
    obj.update(schema='shieldd-transfer-fixed-spend-v1', scope=fixed.SCOPE,
               repeated_observations_equal=True, window_start=0, window_count=1, total_windows=126,
               randomizer=copy.deepcopy(spend['randomizer']), generator=copy.deepcopy(spend['generator']),
               bits=copy.deepcopy(spend['bits']), output=copy.deepcopy(spend['contribution']))
    zero, one = fixtures.native(0), fixtures.native(1)
    generator = spend['generator']; identity = [zero,one]
    selected_y = fixtures.source(2,600)
    # Generator (0,-1) is a curve point; table entries 2/4 are identity.
    obj['windows'] = [dict(bits=copy.deepcopy(spend['bits'][:2]),
                          table=[generator,identity,generator,identity],
                          points=[identity,[zero,selected_y],[zero,selected_y]],
                          arithmetic=[zero,selected_y,selected_y,zero],
                          quotient=[zero,selected_y,one,one,zero,selected_y])]
    required = {tuple(bit) for bit in obj['bits']}
    for value in [obj['randomizer'],*obj['output']]: required.add(tuple(value['source']))
    expressions = {tuple(item['source']):copy.deepcopy(item) for item in base.obj['expressions']}
    required.add((2,600))
    expressions[(2,600)] = dict(source=[2,600], terms=[[0,f'{1:064x}'],[103,f'{fixed.P-2:064x}']])
    steps=[]; previous=one
    def lc(ref):
        if 'native' in ref: return canonical([(0,int(ref['native'],16))])
        return tuple((column,int(coefficient,16)) for column,coefficient in expressions[tuple(ref['source'])]['terms'])
    def node(index, terms):
        required.add((2,index))
        expressions[(2,index)] = dict(source=[2,index],terms=[[column,f'{coefficient:064x}'] for column,coefficient in terms])
        return fixtures.source(2,index)
    for i,bit in enumerate(obj['bits']):
        flag=(ORDER-1)>>i & 1
        bit_ref={'source':bit}; bit_lc=lc(bit_ref)
        factor_lc=bit_lc if flag else combine(((0,1),),bit_lc,-1)
        factor=node(12000+i,factor_lc)
        product_lc=factor_lc if i==0 else ((500+i,1),)
        product=node(10000+i,product_lc)
        after_lc=combine(combine(product_lc,bit_lc,-1),((0,1),)) if flag else product_lc
        after=node(11000+i,after_lc)
        steps.append([previous,bit_ref,fixtures.native(flag),factor,product,after]);previous=after
    obj['canonical']=dict(endpoint=previous['source'],steps=steps)
    obj['expressions'] = [expressions[index] for index in sorted(required)]
    return obj, accepted


class FixedSpendTests(unittest.TestCase):
    def check(self, obj, accepted):
        return fixed.inspect_metadata(fixtures.encoded(obj), accepted)

    def test_typed_fixture_returns_pending_product_quotient_obligations(self):
        obj,accepted=fixture(); checked=self.check(obj,accepted)
        self.assertEqual(len(checked['products']),6)
        self.assertEqual(len(checked['quotients']),2)
        self.assertEqual(len(checked['canonical_products']),251)
        with self.assertRaisesRegex(relation.RelationError,'all126'):
            fixed.join_chunks([checked])

    def test_native_table_recurrence_refuses_changed_coordinate(self):
        obj,accepted=fixture(); obj['windows'][0]['table'][1][0]=fixtures.native(2)
        with self.assertRaisesRegex(relation.RelationError,'recurrence'):
            self.check(obj,accepted)

    def test_quotient_formula_refuses_numerator_or_output_substitution(self):
        for position in (0,4):
            obj,accepted=fixture(); obj['windows'][0]['quotient'][position]=fixtures.native(1)
            with self.assertRaisesRegex(relation.RelationError,'quotient formula'):
                self.check(obj,accepted)

    def test_bit_order_and_bool_indices_fail_closed(self):
        for change in ('swap','bool'):
            obj,accepted=fixture()
            if change=='swap': obj['windows'][0]['bits'].reverse()
            else: obj['bits'][0]=[True,100]
            with self.assertRaises(relation.RelationError): self.check(obj,accepted)

    def test_shared_node_lc_change_refuses_same_handle(self):
        obj,accepted=fixture()
        index=tuple(obj['output'][0]['source'])
        next(item for item in obj['expressions'] if tuple(item['source'])==index)['terms']=[[700,f'{1:064x}']]
        with self.assertRaisesRegex(relation.RelationError,'shared source LC'):
            self.check(obj,accepted)

    def test_folded_selector_semantic_failure(self):
        obj,accepted=fixture()
        # Preserve source identities/formula roles while changing selected y.
        next(item for item in obj['expressions'] if item['source']==[2,600])['terms']=[[0,f'{1:064x}']]
        with self.assertRaisesRegex(relation.RelationError,'folded product'):
            self.check(obj,accepted)

    def test_metadata_parity_bounds_and_closed_shapes_refuse(self):
        for key,value in [('repeated_observations_equal',1),('window_count',17),
                          ('constant_copy',True),('domain_size',1000),('unexpected',0)]:
            obj,accepted=fixture(); obj[key]=value
            with self.assertRaises(relation.RelationError): self.check(obj,accepted)

    def test_native_codec_and_missing_lc_refuse(self):
        obj,accepted=fixture(); obj['generator'][0]={'native':f'{fixed.P:064x}'}
        with self.assertRaises(relation.RelationError): self.check(obj,accepted)
        obj,accepted=fixture(); obj['expressions'].pop()
        with self.assertRaises(relation.RelationError): self.check(obj,accepted)

    def test_canonical_step_order_literal_endpoint_and_recurrence_refuse(self):
        for change in ('literal','endpoint','order','recurrence'):
            obj,accepted=fixture()
            if change=='literal':obj['canonical']['steps'][4][2]=fixtures.native(2)
            elif change=='endpoint':obj['canonical']['endpoint']=[2,600]
            elif change=='order':obj['canonical']['steps'][2][1]=obj['canonical']['steps'][3][1]
            else:
                handle=obj['canonical']['steps'][2][3]['source']
                next(item for item in obj['expressions'] if item['source']==handle)['terms']=[]
            with self.assertRaisesRegex(relation.RelationError,'canonical'):
                self.check(obj,accepted)


if __name__=='__main__': unittest.main()
