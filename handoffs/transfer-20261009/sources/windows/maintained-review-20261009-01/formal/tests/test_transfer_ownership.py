import json
import copy
import unittest
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch
from circuits import transfer_ownership as ownership
from circuits.transfer_relation import MODULUS as P, RelationError


def evaluate(graph, values):
    out=[]
    for node in graph['nodes']:
        kind=node['kind']
        if kind=='input':value=values[node['slot']]
        elif kind=='constant':value=node['value']
        elif kind=='add':value=out[node['left']]+out[node['right']]
        elif kind=='mul':value=out[node['left']]*out[node['right']]
        else:raise AssertionError(kind)
        out.append(value%P)
    return out[graph['output']]


class OwnershipFormulaTests(unittest.TestCase):
    def test_optimized_double_needs_on_curve_premise(self):
        inputs=[('native',0),('native',0)]
        values={}
        for kind in ('numerator','denominator'):
            for axis in ('x','y'):
                graph,roles=ownership.expected_formula('double.'+kind,axis,inputs)
                self.assertEqual(roles,[])
                values[kind,axis]=evaluate(graph,[])
        self.assertEqual(values,{('numerator','x'):0,('numerator','y'):0,
                                 ('denominator','x'):0,('denominator','y'):2})
        # Arbitrary x quotient1 satisfies these two equations while the complete
        # affine formula at (0,0)+(0,0) has x0. This is algebra-only, not a
        # satisfying full ownership/Transfer row assignment.
        output=(1,0)
        self.assertEqual(output[0]*values['denominator','x'],values['numerator','x'])
        self.assertEqual(output[1]*values['denominator','y'],values['numerator','y'])
        self.assertNotEqual(output,(0,0))
        x,y=0,0
        d=(-10240*pow(10241,-1,P))%P
        self.assertNotEqual((y*y-x*x)%P,(1+d*x*x*y*y)%P)

    def test_selector_four_digits(self):
        source=[('source',(1,i)) for i in range(8)]
        for low in (0,1):
            for high in (0,1):
                values=[3,5,7,11,13,17,low,high]
                wanted=((0,1),(3,5),(7,11),(13,17))[low+2*high]
                for axis,value in zip(('x','y'),wanted):
                    graph,roles=ownership.expected_formula('select',axis,source)
                    self.assertEqual(roles,[s[1] for s in source])
                    self.assertEqual(evaluate(graph,values),value)

    def test_native_negation_retains_merge_operand_order(self):
        inputs=[('source',(1,i)) for i in range(8)]
        graph,_=ownership.expected_formula('select','x',inputs)
        # Native0 negation remains Native0, so base.x - 0 is ordered 0 + base.x.
        matches=[n for n in graph['nodes'] if n['kind']=='add' and
                 graph['nodes'][n['left']]=={'kind':'constant','value':0} and
                 graph['nodes'][n['right']]=={'kind':'input','slot':0}]
        self.assertEqual(len(matches),1)

    def test_ingress_schema_control_reaches_schema(self):
        for value in ({},[],True):
            data=(json.dumps(value)+'\n').encode()
            reason='unknown ownership schema/scope' if isinstance(value,dict) else 'record must be a JSON object'
            with self.assertRaisesRegex(RelationError,reason):
                ownership.inspect_metadata(data,'0'*64,[],[],[1,0])

    def test_rnk_ingress_schema_controls_are_distinct(self):
        for value in ({}, [], True):
            data=(json.dumps(value)+'\n').encode()
            reason='unknown ownership schema/scope' if isinstance(value,dict) else 'record must be a JSON object'
            with self.assertRaisesRegex(RelationError,reason):
                ownership.inspect_rnk_metadata(data,'0'*64,[],[],[1,0])



class OwnershipChunkJoinTests(unittest.TestCase):
    """Synthetic already-parsed join inputs; no runtime ingress/proof claim."""
    def chunks(self):
        chunks=[];point=(('source',(1,99)),('source',(1,100)))
        for start in range(0,126,16):
            count=min(16,126-start)
            metadata={key:None for key in ('relation_digest','domain_size','full_rows','constant_copy',
                'ivk_handles','remainder','remainder_bits','total_windows','bits','base','twice','triple','output','target')}
            metadata.update(window_start=start,window_count=count)
            chunks.append({'metadata':metadata,'windows':[(point,point,point,point,point)]*count,
                'expressions':{(1,99):((102,1),)},'nodes':{(2,10):(False,(1,99),(1,100))},
                'quotients':[('pre0',),('pre1',)]})
        return chunks

    def test_complete_ordered_join(self):
        joined=ownership.join_chunks(self.chunks())
        self.assertEqual((joined['windows'],joined['chunks']),(126,8))

    def test_shared_source_and_precomputation_mutations(self):
        original=self.chunks()
        for kind,reason in (('node','shared source node'),('lc','shared source LC'),
                            ('precompute','precomputation source'),('offset','omit/reorder/duplicate')):
            mutated=copy.deepcopy(original)
            if kind=='node':mutated[1]['nodes'][(2,10)]=(True,(1,99),(1,100))
            elif kind=='lc':mutated[1]['expressions'][(1,99)]=((103,1),)
            elif kind=='precompute':mutated[1]['quotients'][0]=('changed',)
            else:mutated[1]['metadata']['window_start']=17
            with self.assertRaisesRegex(RelationError,reason):ownership.join_chunks(mutated)


class OwnershipQuotientTransportTests(unittest.TestCase):
    def fixture(self):
        sources=[('source',(1,i)) for i in range(3)]
        checked={'metadata':{'relation_digest':'a'*64,'constant_copy':10,'domain_size':16,
                            'full_rows':4,'window_start':0,'window_count':1},
                 'derived':{(1,i):((3+i,1),) for i in range(3)},'nodes':{},
                 'quotients':[(sources[0],sources[0],sources[1],sources[1],sources[2],sources[2])]}
        def row(index,a,b=()):
            return {'row':index,'a':[[c,f'{v%P:064x}'] for c,v in sorted(a)],
                    'b':[[c,f'{v%P:064x}'] for c,v in sorted(b)]}
        rows=[row(0,[(0,1),(10,-1)]),row(1,[(4,-1),(5,1)],[(8,1)]),
              row(2,[(4,1),(5,1)],[(8,1),(9,4)]),row(3,[(3,-1),(9,1)])]
        return checked,rows

    def run_extraction(self,checked,rows):
        def inspect(stream,expected_relation,row_observer):
            for row in rows:row_observer(row)
            return {'domain_size':16,'stored_rows':checked['metadata']['full_rows']}
        with patch.object(ownership,'match_formulas'),patch.object(ownership.relation,'inspect',side_effect=inspect):
            return ownership.extract_rows(checked,None,'a'*64)

    def test_materialized_div_product_requires_separate_assertion(self):
        checked,rows=self.fixture()
        result=self.run_extraction(checked,rows)
        self.assertEqual(result['products'][0]['rows'],[1,2,3])
        for omitted in (1,2,3):
            with self.assertRaisesRegex(RelationError,'missing ownership materialized product/assertion'):
                self.run_extraction(checked,[r for r in rows if r['row']!=omitted])

    def test_quotient_certificate_keeps_product_and_assertion(self):
        checked,rows=self.fixture()
        checked['quotients']*=5
        extracted=self.run_extraction(checked,rows)
        extracted['identity']['relation_digest']='a'*64
        selected=ownership.quotient_certificates(checked,extracted)
        self.assertEqual(len(selected['certificates']),10)
        self.assertEqual(selected['certificates'][0]['rows'],[1,2,3])
        self.assertEqual(selected['certificates'][0]['output'],((9,1),))
        source=ownership.generate_quotient_boundaries(selected,'b'*64,'a'*64)
        self.assertIn('Compiler.checked_product_sound',source)
        self.assertIn('Compiler.checked_assertion_sound',source)
        self.assertIn('#check @equation0_sound',source)
        self.assertNotIn('denominatorNonzero',source)
        duplicate=copy.deepcopy(extracted)
        duplicate['products'].append(duplicate['products'][0])
        with self.assertRaisesRegex(RelationError,'duplicate ownership quotient product role'):
            ownership.quotient_certificates(checked,duplicate)
        changed=copy.deepcopy(extracted)
        changed['selected_rows'][-1]['a'][0][1]=f'{1:064x}'
        with self.assertRaisesRegex(RelationError,'materialized assertion mismatch'):
            ownership.quotient_certificates(checked,changed)

    def test_node_operands_with_constant_lcs_fold_without_product_rows(self):
        checked,rows=self.fixture()
        checked['derived'].update({(2,20):(),(2,21):((4,1),),(2,22):()})
        checked['nodes'][(2,22)]=(True,(2,20),(2,21))
        self.assertEqual(len(self.run_extraction(checked,rows)['products']),2)
        checked['derived'][(2,20)]=((0,2),)
        checked['derived'][(2,22)]=((4,2),)
        self.run_extraction(checked,rows)
        checked['derived'][(2,22)]=((4,3),)
        with self.assertRaisesRegex(RelationError,'folded product LC mismatch'):
            self.run_extraction(checked,rows)

    def test_div_equal_linear_operands_use_materialized_square(self):
        checked,rows=self.fixture()
        checked['derived'][(1,2)]=checked['derived'][(1,1)]
        checked['quotients']*=5
        checked['metadata']['full_rows']=3
        rows=[rows[0],{'row':1,'a':[[4,f'{1:064x}']],
                      'b':[[9,f'{1:064x}']]},
              {**rows[3],'row':2}]
        extracted=self.run_extraction(checked,rows)
        extracted['identity']['relation_digest']='a'*64
        selected=ownership.quotient_certificates(checked,extracted)
        self.assertEqual(selected['certificates'][0]['kind'],'square')
        self.assertIn('Compiler.checked_square_sound',
                      ownership.generate_quotient_boundaries(selected,'b'*64,'a'*64))
        with self.assertRaisesRegex(RelationError,'missing ownership materialized square/assertion'):
            self.run_extraction(checked,rows[:-1])

    def test_equal_linear_operands_use_square_despite_distinct_source_handles(self):
        checked,rows=self.fixture()
        checked['metadata']['full_rows']=5
        checked['derived'].update({(2,20):((4,1),),(2,21):((4,1),),(2,22):((7,1),)})
        checked['nodes'][(2,22)]=(True,(2,20),(2,21))
        rows.append({'row':4,'a':[[4,f'{1:064x}']],'b':[[7,f'{1:064x}']]})
        result=self.run_extraction(checked,rows)
        self.assertTrue(any(t['roles']==['node.22.square'] and t['row']==4 for t in result['templates']))
        with self.assertRaisesRegex(RelationError,'missing ownership actual template node.22.square'):
            self.run_extraction(checked,rows[:-1])


class OwnershipPolynomialGeneratorTests(unittest.TestCase):
    def test_first_window_control_refuses_noninitial_observation(self):
        from tests.transfer_ownership_fixture import symbolic_window
        checked,extracted=symbolic_window()
        with self.assertRaisesRegex(RelationError,'requires global window zero'):
            ownership.first_window_controls(checked,extracted)
        with self.assertRaisesRegex(RelationError,'requires global window zero'):
            ownership.generate_first_group_window(checked,extracted)

    def test_symbolic_noninitial_window_composes_original_row_equations(self):
        from tests.transfer_ownership_fixture import symbolic_window
        checked,extracted=symbolic_window()
        self.assertEqual(checked['metadata']['window_start'],1)
        source=ownership.generate_window_equations(checked,extracted,'b'*64,
                                                   namespace='OwnershipSymbolicArithmeticPilot')
        self.assertIn('theorem arithmetic_window',source)
        self.assertIn('Satisfies rho rawRows',source)
        self.assertIn('TransferOwnership.DoubleEquations',source)
        self.assertIn('TransferOwnership.AddEquations',source)
        self.assertIn('List.mem_append.mpr (Or.inl member)',source)
        self.assertIn('List.mem_append.mpr (Or.inr member)',source)
        self.assertEqual(source.count('#check @arithmetic_window'),1)
        self.assertNotIn('linear_combination',source)
        # A partially folded denominator can mention its own constant LC on
        # the RHS. Repeated simp rewrites would expand that equality forever.
        self.assertNotIn('simp only [n, d] at equation',source)
        self.assertEqual(source.count('rw [n] at equation'),10)
        self.assertEqual(source.count('try rw [d] at equation'),10)
        window_only=ownership.generate_window_equations(checked,extracted,'b'*64,
            namespace='OwnershipSymbolicWindowOnly',include_precompute=False)
        self.assertNotIn('DoubleEquations (base rho) (twice rho)',window_only)
        self.assertEqual(window_only.count('rw [n] at equation'),6)
        self.assertIn('DoubleEquations (input rho) (first rho)',window_only)
        renamed=ownership.window_renaming(checked,extracted,checked,extracted)
        self.assertTrue(all(left==right for left,right in renamed['columns']))
        self.assertTrue(all(left==right for left,right in renamed['row_targets']))
        instance=ownership.generate_renamed_window(checked,extracted,checked,extracted)
        self.assertIn('RowRenaming.checked_rows',instance)
        self.assertIn('RowRenaming.checked_linear',instance)
        self.assertIn('fun column => rho (columns column)',instance)
        self.assertEqual(instance.count('#check @arithmetic_window'),1)

    def test_bounded_independent_graph_is_rendered(self):
        from circuits.generate_group_cones import expected_graph_formula
        graph={'arity':2,'nodes':[{'kind':'input','slot':0},{'kind':'input','slot':1},
                                {'kind':'add','left':0,'right':1}],'output':2}
        self.assertEqual(expected_graph_formula(graph,['a','b']),'((eval rho a) + (eval rho b))')
        for kind in ('alias','forward','coefficient'):
            mutant=copy.deepcopy(graph)
            if kind=='alias':mutant['nodes'][0]['slot']=True
            elif kind=='forward':mutant['nodes'][2]['right']=2
            else:mutant['nodes'][0]={'kind':'constant','value':P}
            with self.assertRaises(ValueError):expected_graph_formula(mutant,['a','b'])

    def test_selector_axis_keeps_unused_declared_input_slots(self):
        from circuits.generate_group_cones import generate_checked
        for axis in ('x','y'):
            inputs=[('source',(1,i)) for i in range(8)]
            graph,_=ownership.expected_formula('select',axis,inputs)
            derived={(1,i):((3+i,1),) for i in range(8)}
            source={f'w{i}':{'kind':'witness'} for i in range(8)}
            names=[];rows=[(ownership.canonical([(0,1),(3000,-1)]),())]
            def add_row(a,b):
                rows.append(tuple(ownership.canonical((3000 if c==0 else c,v) for c,v in lc) for lc in (a,b)))
            for index,node in enumerate(graph['nodes']):
                kind=node['kind']
                if kind=='input':handle=(1,node['slot']);name='w'+str(node['slot'])
                elif kind=='constant':
                    handle=(0,index);name='c'+str(index)
                    source[name]={'kind':'constant','value':node['value']}
                    derived[handle]=ownership.canonical([(0,node['value'])])
                else:
                    handle=(2,index);name='n'+str(index)
                    left,right=names[node['left']],names[node['right']]
                    source[name]={'kind':kind,'left':left[1],'right':right[1]}
                    a,b=derived[left[0]],derived[right[0]]
                    if kind=='add':derived[handle]=ownership.combine(a,b)
                    else:
                        folded=next(((lc,other) for lc,other in ((a,b),(b,a))
                                     if not lc or len(lc)==1 and lc[0][0]==0),None)
                        if folded:
                            constant,other=folded;coefficient=constant[0][1] if constant else 0
                            derived[handle]=ownership.canonical((c,v*coefficient) for c,v in other)
                        else:
                            out=((100+index,1),);derived[handle]=out
                            if a==b:add_row(a,out)
                            else:
                                auxiliary=((1000+index,1),)
                                add_row(ownership.combine(a,b,-1),auxiliary)
                                add_row(ownership.combine(a,b),ownership.combine(auxiliary,out,4))
                names.append((handle,name))
            output=names[graph['output']]
            visited=set()
            def visit(name):
                if name in visited:return
                visited.add(name);node=source[name]
                if node['kind'] in ('add','mul'):visit(node['left']);visit(node['right'])
            visit(output[1])
            cone={'kind':'select','axis':axis,'inputs':inputs,'output':('source',output[0]),
                  'graph':graph,'pairs':[(i,name) for i,name in enumerate(sorted(visited))]}
            metadata={'relation_digest':'a'*64,'domain_size':4096,'full_rows':len(rows),
                      'constant_copy':3000,'window_count':1}
            checked={'metadata':metadata,'derived':derived}
            encoded=[{'row':i,'a':[[c,f'{v:064x}'] for c,v in a],
                      'b':[[c,f'{v:064x}'] for c,v in b]} for i,(a,b) in enumerate(rows)]
            extracted={'identity':{'relation_digest':'a'*64,'stored_rows':len(rows),'domain_size':4096},
                       'selected_rows':encoded}
            with patch.object(ownership,'match_formulas',return_value={'source':source,'cones':[cone]*22}):
                selected=ownership.cone_certificates(checked,extracted,include_precompute=False)
            generated=generate_checked(selected,'b'*64,'a'*64,namespace='OwnershipSelectorFixture')
            for slot in range(8):self.assertIn('def formula8_w'+str(slot)+' : Linear',generated)


class OwnershipCliTests(unittest.TestCase):
    def run_cli(self,*arguments):
        import security
        with patch.object(sys,'argv',['security.py','check',*arguments]), \
             patch.object(security,'check_register',return_value={}):
            return security.main()

    def test_requires_both_current_role_inputs(self):
        self.assertEqual(self.run_cli('--relation-export','unused','--expected-relation-digest','1'*64,
                                     '--ownership-inspection','unused','--ivk-inspection','unused'),1)
        self.assertEqual(self.run_cli('--relation-export','unused','--expected-relation-digest','1'*64,
                                     '--ownership-window-candidate','unused.lean'),1)

    def test_complete_candidates_require_exact_roles_and_refuse_qualification(self):
        self.assertEqual(self.run_cli('--ownership-chunks', 'unused'), 1)
        arguments = ['--relation-export', 'rows', '--expected-relation-digest', '1' * 64,
                     '--ivk-inspection', 'ivk', '--ivk-reduction-inspection', 'reduction',
                     '--ownership-chunks', *[f'chunk{i}' for i in range(8)],
                     '--ownership-candidates-dir', 'fresh']
        import security
        with patch.object(security, 'prepare_ownership_candidates', return_value={'scope': 'diagnostic only'}) as prepare:
            self.assertEqual(self.run_cli(*arguments), 0)
            self.assertEqual(len(prepare.call_args.args[0].ownership_chunks), 8)
            prepare.reset_mock()
            for conflict in ('--verify-link', '--ownership-inspection', '--ownership-window-candidate'):
                extra = [conflict] if conflict == '--verify-link' else [conflict, 'mixed']
                self.assertEqual(self.run_cli(*arguments, *extra), 1)
                prepare.assert_not_called()


    def test_candidate_source_is_fresh_and_preserves_existing_file(self):
        import security
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'candidate.lean'
            security.write_ownership_candidate(path,'-- diagnostic source\n')
            self.assertEqual(path.read_bytes(),b'-- diagnostic source\n')
            with self.assertRaises(FileExistsError):
                security.write_ownership_candidate(path,'changed\n')
            self.assertEqual(path.read_bytes(),b'-- diagnostic source\n')
            with self.assertRaisesRegex(security.CheckError,'fresh .lean'):
                security.write_ownership_candidate(Path(directory)/'evidence.json','unused')

    def test_refuses_qualification_and_mixed_slices(self):
        self.assertEqual(self.run_cli('--ownership-inspection','unused','--verify-link'),1)
        self.assertEqual(self.run_cli('--relation-export','unused','--expected-relation-digest','1'*64,
            '--ownership-inspection','unused','--ivk-inspection','unused',
            '--ivk-reduction-inspection','unused','--ak-subgroup-inspection','unused'),1)

    def test_routes_retained_ivk_remainder_and_bit_roles(self):
        handles=[[1,1990],[1,1977],[1,1978],[2,329976]]
        bits=[[1,i] for i in range(252)];remainder=[1,123]
        with tempfile.TemporaryDirectory() as directory:
            path=Path(directory)/'metadata';path.write_bytes(b'{}\n')
            observed={'metadata':{'window_start':1,'window_count':1,
                       'domain_size':16,'full_rows':4,'constant_copy':10}}
            with patch('circuits.transfer_ivk_rows.inspect_metadata',return_value={'metadata':{'handles':handles}}), \
                 patch('circuits.transfer_ivk_reduction.inspect_metadata',return_value={'metadata':{
                     'remainder_bits':bits,'remainder':remainder,
                     'domain_size':16,'stored_rows':4,'constant_copy':10}}), \
                 patch.object(ownership,'inspect_metadata',return_value=observed) as ingress, \
                 patch.object(ownership,'extract_rows',return_value={'selected_rows':[{}],
                     'products':[],'scope':'extraction only'}) as extract:
                self.assertEqual(self.run_cli('--relation-export',str(path),'--expected-relation-digest','1'*64,
                    '--ownership-inspection',str(path),'--ivk-inspection',str(path),
                    '--ivk-reduction-inspection',str(path)),0)
                self.assertEqual(ingress.call_args.args[2:],(handles,bits,remainder))
                self.assertIs(extract.call_args.args[0],observed)
                self.assertEqual(extract.call_args.args[2],'1'*64)
                candidate=Path(directory)/'window.lean'
                with patch.object(ownership,'generate_window_equations',return_value='-- generated diagnostic\n') as generate:
                    self.assertEqual(self.run_cli('--relation-export',str(path),'--expected-relation-digest','1'*64,
                        '--ownership-inspection',str(path),'--ivk-inspection',str(path),
                        '--ivk-reduction-inspection',str(path),'--ownership-window-candidate',str(candidate)),0)
                    self.assertIs(generate.call_args.args[0],observed)
                    self.assertEqual(generate.call_args.kwargs,{'window_offset':0,'namespace':'RuntimeOwnershipWindow001'})
                    self.assertEqual(candidate.read_bytes(),b'-- generated diagnostic\n')
                    self.assertEqual(self.run_cli('--relation-export',str(path),'--expected-relation-digest','1'*64,
                        '--ownership-inspection',str(path),'--ivk-inspection',str(path),
                        '--ivk-reduction-inspection',str(path),'--ownership-window-candidate',str(Path(directory)/'only.lean'),
                        '--ownership-window-only'),0)
                    self.assertEqual(generate.call_args.kwargs,{'window_offset':0,'namespace':'RuntimeOwnershipWindow001',
                        'include_precompute':False})
                    generate.reset_mock()
                    self.assertEqual(self.run_cli('--relation-export',str(path),'--expected-relation-digest','1'*64,
                        '--ownership-inspection',str(path),'--ivk-inspection',str(path),
                        '--ivk-reduction-inspection',str(path),'--ownership-window-candidate',str(Path(directory)/'outside.lean'),
                        '--ownership-window-offset','1'),1)
                    generate.assert_not_called()
                    observed['metadata']['window_start']=0
                    with patch.object(ownership,'generate_first_group_window',return_value='-- group diagnostic\n') as group:
                        self.assertEqual(self.run_cli('--relation-export',str(path),'--expected-relation-digest','1'*64,
                            '--ownership-inspection',str(path),'--ivk-inspection',str(path),
                            '--ivk-reduction-inspection',str(path),'--ownership-window-candidate',str(Path(directory)/'Arithmetic.lean'),
                            '--ownership-first-group-candidate',str(Path(directory)/'GroupBridge.lean')),0)
                        self.assertEqual(extract.call_args.kwargs,{'include_bits':True})
                        self.assertEqual(group.call_args.kwargs,{'arithmetic_module':'Arithmetic',
                            'arithmetic_namespace':'RuntimeOwnershipWindow000'})
                        self.assertEqual((Path(directory)/'GroupBridge.lean').read_bytes(),b'-- group diagnostic\n')
                observed['metadata']['constant_copy']=11
                extract.reset_mock()
                self.assertEqual(self.run_cli('--relation-export',str(path),'--expected-relation-digest','1'*64,
                    '--ownership-inspection',str(path),'--ivk-inspection',str(path),
                    '--ivk-reduction-inspection',str(path)),1)
                extract.assert_not_called()


class OwnershipTraceGeneratorTests(unittest.TestCase):
    def fixture(self):
        handles = [(1, i) for i in range(252)]
        observed = {'metadata': {'window_start': 0, 'window_count': 1,
                    'relation_digest': 'a' * 64, 'full_rows': 2, 'domain_size': 512},
                    'bits': handles, 'derived': {handles[i]: ((3 + i, 1),) for i in (250, 251)}}
        rows = [{'row': i - 250, 'a': [[3 + i, f'{1:064x}']],
                 'b': [[3 + i, f'{1:064x}']]} for i in (250, 251)]
        extracted = {'identity': {'relation_digest': 'a' * 64, 'stored_rows': 2, 'domain_size': 512},
                     'templates': [{'row': i - 250, 'roles': [f'bit.{i}']} for i in (250, 251)],
                     'selected_rows': rows}
        return observed, extracted

    def test_bounded_trace_uses_rows_and_reconstructed_boolean_values(self):
        observed, extracted = self.fixture()
        source = ownership.generate_trace_chunk(observed, extracted)
        self.assertIn('import ShielddSecurity.RuntimeOwnershipWindow000', source)
        self.assertIn('ScalarBits.checked_bit_value', source)
        self.assertIn('actual_trace_equations', source)
        self.assertIn('window0_equations rho one four satisfied', source)
        self.assertNotIn('baseRole', source)
        self.assertNotIn('codec', source)
        extracted['identity']['stored_rows'] = 3
        with self.assertRaisesRegex(RelationError, 'identity/shape'):
            ownership.generate_trace_chunk(observed, extracted)

    def test_boolean_row_and_complete_control_ingress_fail_closed(self):
        observed, extracted = self.fixture()
        extracted['selected_rows'][0]['b'] = []
        with self.assertRaisesRegex(RelationError, 'wrong Boolean role'):
            ownership.generate_trace_chunk(observed, extracted)
        with self.assertRaises(RelationError):
            ownership.endpoint_controls([observed], [extracted])





class CofactorSubstitutionIngressTests(unittest.TestCase):
    def fixture(self):
        digest = '1' * 64
        rows = [{'row': i, 'a': [[1980 if i == 0 else 1981 if i == 1 else 20+i, '1'.zfill(64)]], 'b': []} for i in range(73)]
        rows.append({'row': 73, 'a': [[0, '1'.zfill(64)], [3000, format(P-1, '064x')]], 'b': []})
        identity = {'relation_digest': digest, 'domain_size': 4096, 'stored_rows': 74}
        columns = {c: c for row in rows for key in ('a', 'b') for c, _ in row[key]}
        request = {'namespace': 'SyntheticSender', 'columns': columns,
                   'point': [[(1980, 1)], [(1981, 1)]]}
        return {'identity': identity, 'selected_rows': rows}, request, digest

    def test_wrong_claimed_point_is_refused_before_stream(self):
        template, request, digest = self.fixture()
        request['point'][0] = [(1981, 1)]
        with patch.object(ownership.relation, 'inspect') as inspect:
            with self.assertRaisesRegex(RelationError, '^cofactor substitution claimed point mismatch$'):
                ownership.extract_cofactor_substitutions(template, [request], None, digest)
            inspect.assert_not_called()

    def test_complete_rows_and_intended_missing_row_refusal(self):
        template, request, digest = self.fixture()
        def replay(stream, expected_relation, row_observer):
            self.assertEqual(expected_relation, digest)
            for row in stream:
                row_observer(row)
            return template['identity']
        with patch.object(ownership.relation, 'inspect', side_effect=replay):
            result = ownership.extract_cofactor_substitutions(template, [request], template['selected_rows'], digest)
            self.assertEqual(len(result[0]['selected_rows']), 74)
            with self.assertRaisesRegex(RelationError, '^missing actual renamed cofactor row$'):
                ownership.extract_cofactor_substitutions(template, [request], template['selected_rows'][1:], digest)

class CofactorCandidateCliTests(unittest.TestCase):
    def test_template_cannot_be_silently_ignored_without_complete_candidates(self):
        import security
        with patch.object(sys, 'argv', ['security.py', 'check', '--ownership-cofactor-template', 'template.json']), \
             patch.object(security, 'prepare_ownership_candidates') as generate:
            self.assertEqual(security.main(), 1)
            generate.assert_not_called()


if __name__=='__main__':unittest.main()
