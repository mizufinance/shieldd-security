"""Synthetic bounded source fixture; no actual capture or qualification credit."""
import copy,json,unittest
from unittest.mock import patch
from circuits import transfer_balance_variable as variable,transfer_relation as relation
from tests.transfer_ownership_fixture import symbolic_window


def balance_rows(rows):
    relocated=copy.deepcopy(rows)
    for row in relocated:
        for key in ('a','b'):
            row[key]=sorted([[17 if c==6 else c,value] for c,value in row[key]])
    return relocated


def fixture():
    checked,_=symbolic_window();bits=checked['bits'][122:251]
    native=lambda v:{'native':f'{v:064x}'}
    def observed(value):return {'source':list(value[1])} if value[0]=='source' else native(value[1])
    def point(value):return [observed(v) for v in value]
    p=checked['points'];q=checked['quotients'];window=checked['windows'][0]
    obj=dict(schema='shieldd-transfer-balance-variable-v1',family='transfer',scope=variable.SCOPE,
        relation_digest='a'*64,domain_size=16384,full_rows=checked['metadata']['full_rows'],constant_copy=16000,
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,
        window_start=1,window_count=1,total_windows=65,bit_width=129,
        negative={'source':[1,500]},magnitude={'source':[1,501]},base=point(p['base']),twice=point(p['twice']),
        triple=point(p['triple']),output=point(p['output']),bits=[list(bit) for bit in bits],
        precompute_quotients=[[observed(v) for v in quotient] for quotient in q[:2]],
        windows=[dict(index=1,points=[point(value) for value in window],
            bits=[{'source':list(bits[126])},{'source':list(bits[127])}],quotients=[[observed(v) for v in quotient] for quotient in q[2:]])])
    roots=set(bits)|{(1,500),(1,501)}
    for values in [*p.values(),*q]:
        roots.update(v[1] for v in values if v[0]=='source')
    roots.update(v[1] for point_value in window for v in point_value if v[0]=='source')
    pending=list(roots);visited=set();required=set(roots)
    while pending:
        source=pending.pop()
        if source in visited:continue
        visited.add(source)
        if source[0]==2:
            multiply,left,right=checked['nodes'][source]
            if multiply and left[0]!=0 and right[0]!=0:required.update((source,left,right))
            pending.extend((left,right))
        else:required.add(source)
    expressions=dict(checked['derived']);expressions.update({(1,500):((503,1),),(1,501):((504,1),)})
    # This balance-only fixture must leave the original asset witness6 outside
    # its table construction. The generic ownership fixture uses6 as an
    # anonymous table pivot; relocate that fixture coordinate to unused17.
    obj['expressions']=[dict(source=list(source),terms=sorted([[17 if c==6 else c,f'{v:064x}'] for c,v in expressions[source]])) for source in sorted(required)]
    obj['nodes']=[dict(index=source[1],multiply=m,left=list(l),right=list(r)) for source,(m,l,r) in sorted(checked['nodes'].items()) if source in visited]
    def move_table_witness(value):
        if isinstance(value,list):
            if value==[1,3]:return [1,14]
            return [move_table_witness(item) for item in value]
        if isinstance(value,dict):return {key:move_table_witness(item) for key,item in value.items()}
        return value
    # Witness14 really lowers to column17. Rename its source references too;
    # changing only the LC would violate the pinned witness-index ABI.
    obj=move_table_witness(obj)
    obj['expressions'].sort(key=lambda item:tuple(item['source']))
    signed=dict(identity={'relation_digest':'a'*64},copy=16000,negative=503,magnitude=504,bits=[i+3 for _,i in bits],metadata_sha256='b'*64)
    return obj,signed,obj['base']


class BalanceVariableIngressTests(unittest.TestCase):
    def test_raw_derivative_flags_are_retained_and_parent_descriptors_refuse(self):
        metadata,signed,base=fixture()
        metadata.update(ordinary_full_ordered_rows_equal=False,repeated_observations_equal=False)
        raw=(json.dumps(metadata)+'\n').encode()
        with self.assertRaises(relation.RelationError):variable.inspect_metadata(raw,'a'*64,signed,base)
        derivative=variable._inspect_metadata(raw,'a'*64,signed,base,'c'*64)
        self.assertFalse(derivative['metadata']['ordinary_full_ordered_rows_equal'])
        self.assertFalse(derivative['metadata']['repeated_observations_equal'])
        self.assertEqual(derivative['qualification_parent_sha256'],'c'*64)
        parent=dict(schema='shieldd-transfer-balance-variable-pages-v1',family='transfer',
            scope='5 bounded balance129 window pages from one lowering; group/native joins open',
            relation_digest='a'*64,domain_size=16384,full_rows=100,constant_copy=16000,
            ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,pages=[])
        import blake3
        for ordinal in range(5):parent['pages'].append(dict(ordinal=ordinal,window_start=16*ordinal,
            window_count=min(16,65-16*ordinal),blake3=blake3.blake3(raw).hexdigest()))
        # A correctly hashed wrong local window cannot be promoted to page0.
        with self.assertRaisesRegex(relation.RelationError,'qualified-parent identity'):
            variable.inspect_pages((json.dumps(parent)+'\n').encode(),[raw]*5,'a'*64,signed,base)
        for mutate in (lambda p:p.update(repeated_observations_equal=False),lambda p:p['pages'].pop(),
                       lambda p:p['pages'][0].update(ordinal=1),lambda p:p['pages'][0].update(blake3='0'*64)):
            damaged=copy.deepcopy(parent);mutate(damaged)
            with self.assertRaises(relation.RelationError):
                variable.inspect_pages((json.dumps(damaged)+'\n').encode(),[raw]*5,'a'*64,signed,base)

    def test_computed_role_boundaries_keep_actual_node_records(self):
        metadata,signed,_=fixture()
        def replace(value):
            if value==[1,0]:return [2,998]
            if value==[1,1]:return [2,999]
            if isinstance(value,list):return [replace(item) for item in value]
            if isinstance(value,dict):return {key:replace(item) for key,item in value.items()}
            return value
        metadata=replace(metadata)
        # Exact external source operations are retained, without selecting or
        # proving their upstream children in this local window packet.
        metadata['nodes']=[dict(index=i,multiply=True,left=[1,900],right=[1,901]) for i in (998,999)]+metadata['nodes']
        metadata['expressions'].sort(key=lambda item:item['source'])
        checked=variable.inspect_metadata((json.dumps(metadata)+'\n').encode(),'a'*64,signed,metadata['base'])
        self.assertTrue({(2,998),(2,999)}<=checked['boundaries'])
        self.assertNotIn((1,900),checked['expressions'])
        self.assertEqual(len(variable.match_formulas(checked)['cones']),22)
        damaged=copy.deepcopy(metadata);damaged['nodes']=damaged['nodes'][1:]
        with self.assertRaisesRegex(relation.RelationError,'missing source node'):
            variable.inspect_metadata((json.dumps(damaged)+'\n').encode(),'a'*64,signed,damaged['base'])

    def test_all65_chunk_continuity_and_shared_source_refusal(self):
        identity=(('native',0),('native',1));point=[{'native':'0'*64},{'native':'0'*63+'1'}]
        common=dict(schema='shieldd-transfer-balance-variable-v1',scope=variable.SCOPE,relation_digest='a'*64,
            domain_size=16384,full_rows=100,constant_copy=16000,total_windows=65,bit_width=129,
            ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,negative={'source':[1,500]},
            magnitude={'source':[1,501]},base=point,twice=point,triple=point,bits=[[1,i] for i in range(129)],
            output=point,precompute_quotients=[[]]*2)
        chunks=[]
        for start in (0,16,32,48,64):
            count=min(16,65-start);metadata=dict(common,window_start=start,window_count=count)
            chunks.append(dict(metadata=metadata,metadata_sha256=f'{start:064x}',signed_parent_metadata_sha256='b'*64,
                windows=[(identity,)*5]*count,points={'output':identity},quotients=[('pre0',),('pre1',)],
                expressions={(1,500):((503,1),)},nodes={(2,5):(False,(1,500),(1,501))}))
        self.assertEqual(variable.join_chunks(chunks)['windows'],65)
        for mutate in [lambda c:c[1]['metadata'].update(window_start=17),
                       lambda c:c[1]['expressions'].update({(1,500):((503,2),)}),
                       lambda c:c[1]['nodes'].update({(2,5):(True,(1,500),(1,501))}),
                       lambda c:c[1].update(signed_parent_metadata_sha256='c'*64)]:
            damaged=copy.deepcopy(chunks);mutate(damaged)
            with self.assertRaises(relation.RelationError):variable.join_chunks(damaged)

    def test_actual_product_auxiliary_and_quotient_assertion_templates(self):
        metadata,signed,base=fixture()
        checked=variable.inspect_metadata((json.dumps(metadata)+'\n').encode(),'a'*64,signed,base)
        _,original=symbolic_window();rows=balance_rows(original['selected_rows'])
        def replay(stream,expected_relation,row_observer):
            for row in rows:row_observer(row)
            return dict(relation_digest='a'*64,domain_size=16384,stored_rows=metadata['full_rows'])
        with patch.object(variable.relation,'inspect',side_effect=replay):
            extracted=variable.extract_rows(checked,None,'a'*64)
        self.assertTrue(extracted['products'])
        self.assertEqual(extracted['signed_parent_metadata_sha256'],'b'*64)
        # Remove an original quotient assertion; the inferred product alone
        # is insufficient to establish division and the matcher must refuse.
        assertion=next(item['rows'][-1] for item in extracted['products'] if item['role'].startswith('quotient.') and len(item['rows'])==3)
        def missing(stream,expected_relation,row_observer):
            for row in rows:
                if row['row']!=assertion:row_observer(row)
            return dict(relation_digest='a'*64,domain_size=16384,stored_rows=metadata['full_rows'])
        with patch.object(variable.relation,'inspect',side_effect=missing),self.assertRaises(relation.RelationError):
            variable.extract_rows(checked,None,'a'*64)

    def test_exact_source_formulas_and_signed129_parent(self):
        metadata,signed,base=fixture()
        checked=variable.inspect_metadata((json.dumps(metadata)+'\n').encode(),'a'*64,signed,base)
        matched=variable.match_formulas(checked)
        self.assertEqual(len(matched['cones']),22)
        self.assertEqual(len(checked['bits']),129)
        self.assertEqual(checked['window_bits'][0],(('source',checked['bits'][126]),('source',checked['bits'][127])))
        # Independent source mutation changes a real numerator, rather than
        # testing an absent dependency/compiler failure as a semantic control.
        broken=copy.deepcopy(checked);source=checked['quotients'][2][0][1]
        multiply,left,right=broken['nodes'][source];broken['nodes'][source]=(not multiply,left,right)
        with self.assertRaisesRegex(relation.RelationError,'source mismatch'):variable.match_formulas(broken)

    def test_full_scope_roles_padding_and_source_lc_refusals(self):
        metadata,signed,base=fixture()
        changes=[('pending',lambda m:m.update(repeated_observations_equal=False)),
            ('schema',lambda m:m.update(total_windows=126)),
            ('high',lambda m:m['windows'][0]['bits'].__setitem__(1,{'native':'0'*64})),
            ('loop',lambda m:m['windows'][0].update(index=2)),
            ('lc',lambda m:m['expressions'][0]['terms'].append([16000,'0'*63+'1'])),
            ('extra',lambda m:m.update(extra=True))]
        for label,change in changes:
            damaged=copy.deepcopy(metadata);change(damaged)
            with self.subTest(label=label),self.assertRaises(relation.RelationError):
                variable.inspect_metadata((json.dumps(damaged)+'\n').encode(),'a'*64,signed,base)
        wrong=copy.deepcopy(signed);wrong['bits'][0]+=1
        with self.assertRaisesRegex(relation.RelationError,'signed parent'):
            variable.inspect_metadata((json.dumps(metadata)+'\n').encode(),'a'*64,wrong,base)
        with self.assertRaisesRegex(relation.RelationError,'asset-generator'):
            variable.inspect_metadata((json.dumps(metadata)+'\n').encode(),'a'*64,signed,list(reversed(base)))
        # First window requires a native false high; a witnessed zero would
        # introduce an unproved bit/source substitution and is refused.
        damaged=copy.deepcopy(metadata);damaged['window_start']=0;damaged['windows'][0]['index']=0
        damaged['windows'][0]['points'][0]=[{'native':'0'*64},{'native':'0'*63+'1'}]
        damaged['windows'][0]['bits']=[{'source':metadata['bits'][128]},{'source':metadata['bits'][127]}]
        with self.assertRaisesRegex(relation.RelationError,'nativefalse high padding'):
            variable.inspect_metadata((json.dumps(damaged)+'\n').encode(),'a'*64,signed,base)

if __name__=='__main__':unittest.main()
