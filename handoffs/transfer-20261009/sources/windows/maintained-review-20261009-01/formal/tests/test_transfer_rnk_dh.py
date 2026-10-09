"""Synthetic RNK ingress controls; no runtime arithmetic evidence."""
import copy,json,unittest,sys,io
from contextlib import redirect_stderr
from unittest.mock import patch
from circuits import transfer_ownership as o
from circuits.transfer_relation import MODULUS,RelationError
class RnkIngressTests(unittest.TestCase):
    def fixture(self):
        n=lambda x:{'native':f'{x:064x}'}
        w=lambda x:{'source':[1,x]}
        identity=[n(0),n(1)];bits=[[1,i] for i in range(10,262)];ivk=[[1,0],[1,1],[1,2],[2,3]]
        obj={'schema':'shieldd-transfer-rnk-dh-v1','family':'transfer','scope':o.RNK_SCOPE,
          'relation_digest':'a'*64,'domain_size':512,'full_rows':10,'constant_copy':500,
          'ivk_handles':ivk,'remainder':[1,4],'remainder_bits':bits,'bits':bits,
          'window_start':0,'window_count':1,'total_windows':126,'base':[w(5),w(6)],
          'twice':identity,'triple':identity,'output':identity,'windows':[[identity]*5],
          'window_bits':[bits[250:252]],'quotients':[[n(0),n(0),n(1),n(1),n(0),n(1)]]*5,
          'expressions':[{'source':[1,i],'terms':[[3+i,f'{1:064x}']]} for i in sorted([5,6,300]+list(range(10,262)))],
          'nodes':[],'nonidentity_inverse':w(300),'rnk_bindings':{'inputs':identity+[w(350+i) for i in range(7)],
          'hash':w(360),'commitment':w(361),'regulated':w(362),'registered':w(363),'effective_nk':w(364)}}
        return obj,ivk,bits
    def parse(self,obj,ivk,bits):
        return o.inspect_rnk_metadata((json.dumps(obj)+'\n').encode(),'a'*64,ivk,bits,[1,4])
    def test_boundary_refs_are_outside_closed_loop(self):
        obj,ivk,bits=self.fixture();checked=self.parse(obj,ivk,bits)
        self.assertNotIn((1,360),checked['expressions'])
        self.assertEqual(checked['rnk_boundary']['hash'],('source',(1,360)))
        self.assertNotIn('target',checked['points'])
    def test_typed_refusals_reach_expected_checks(self):
        original,ivk,bits=self.fixture()
        for kind,reason in [('schema','unknown ownership schema/scope'),('target','unknown ownership schema/scope'),
          ('dh','RNK DH hash input role mismatch'),('inverse','RNK nonidentity inverse must be witness'),
          ('arity','wrong RNK boundary input arity'),('extra','unknown RNK boundary schema'),
          ('native','noncanonical ownership native value')]:
            obj=copy.deepcopy(original)
            if kind=='schema':obj['schema']='shieldd-transfer-ownership-v1'
            elif kind=='target':obj['target']=obj['output']
            elif kind=='dh':obj['rnk_bindings']['inputs'][0]={'source':[1,5]}
            elif kind=='inverse':obj['nonidentity_inverse']={'native':f'{1:064x}'}
            elif kind=='arity':obj['rnk_bindings']['inputs'].pop()
            elif kind=='extra':obj['rnk_bindings']['extra']=0
            else:obj['rnk_bindings']['hash']={'native':f'{MODULUS:064x}'}
            with self.subTest(kind=kind),self.assertRaisesRegex(RelationError,reason):self.parse(obj,ivk,bits)
class ChunkSubstitutionControls(unittest.TestCase):
    """Isolate merged-map controls using already-parsed synthetic inputs."""
    def inputs(self):
        bits=[(1,i) for i in range(252)]
        checked={'metadata':{'window_start':16,'window_count':2},'bits':bits,
                 'derived':{source:((3+source[1],1),) for source in bits}}
        columns=[(42,42)]+[(3+i,3+i) for i in range(216,220)]
        row=(((42,1),),())
        window={'columns':columns,'row_targets':[(1,2)],'template_rows':{1:row},'actual_rows':{2:row}}
        return checked,copy.deepcopy(checked),window
    def test_merged_map_rejects_conflicting_window_images(self):
        source,target,window=self.inputs();changed=copy.deepcopy(window);changed['columns'][0]=(42,43)
        with patch.object(o,'window_renaming',side_effect=[window,changed]),self.assertRaisesRegex(RelationError,'inconsistent column images'):
            o.chunk_renaming(source,{},target,{})
    def test_active_bit_lc_binding_is_checked(self):
        source,target,window=self.inputs();target['derived'][(1,216)]=((219,2),)
        with patch.object(o,'window_renaming',return_value=window),self.assertRaisesRegex(RelationError,'bit role mismatch'):
            o.chunk_renaming(source,{},target,{})

class RnkCliTests(unittest.TestCase):
    def run_cli(self,arguments,reason):
        import security
        errors=io.StringIO()
        with patch.object(sys,'argv',['security.py','check',*arguments]),patch.object(security,'check_register',return_value={}),redirect_stderr(errors):
            result=security.main()
        self.assertEqual(result,1);self.assertIn(reason,errors.getvalue())
    def test_required_roles_and_mixed_slice_fail_before_reads(self):
        base=['--relation-export','unused','--expected-relation-digest','a'*64,'--rnk-dh-inspection','unused']
        reason='RNK-DH inspection requires matching IVK/reduction without mixed slices'
        self.run_cli(base,reason)
        self.run_cli(base+['--ivk-inspection','unused','--ivk-reduction-inspection','unused','--ownership-inspection','unused'],reason)
    def test_qualification_is_not_an_extraction_route(self):
        self.run_cli(['--relation-export','unused','--expected-relation-digest','a'*64,
                      '--rnk-dh-inspection','unused','--verify-link'],
                     'relation inspection cannot process qualification or publication options')
    def test_complete_owner_candidates_do_not_ignore_rnk_slice(self):
        self.run_cli(['--relation-export','unused','--expected-relation-digest','a'*64,
                      '--rnk-dh-inspection','unused','--ivk-inspection','unused','--ivk-reduction-inspection','unused',
                      '--ownership-candidates-dir','unused','--ownership-chunks',*[f'chunk{i}' for i in range(8)]],
                     'complete ownership candidates require matching IVK/reduction without mixed slices')

class RnkCompositionIngressTests(unittest.TestCase):
    def test_exact_extraction_identity_is_checked(self):
        chunk={'metadata':{'schema':'shieldd-transfer-rnk-dh-v1','relation_digest':'a'*64,
                           'domain_size':512,'full_rows':200}}
        extracted={'identity':{'relation_digest':'a'*64,'domain_size':512,'stored_rows':200}}
        with patch.object(o,'cone_certificates') as cones:
            o._validate_rnk_composition_extraction(chunk,extracted)
            cones.assert_called_once_with(chunk,extracted,window_offset=0,include_precompute=True)
        for key,value in [('relation_digest','b'*64),('domain_size',1024),('stored_rows',201)]:
            changed=copy.deepcopy(extracted);changed['identity'][key]=value
            with self.assertRaisesRegex(RelationError,'extraction identity mismatch'):
                o._validate_rnk_composition_extraction(chunk,changed)
    def test_owner_observation_cannot_supply_rnk_trace(self):
        with self.assertRaisesRegex(RelationError,'requires RNK observations'):
            o._validate_rnk_composition_extraction({'metadata':{'schema':'shieldd-transfer-ownership-v1'}},{})

class RnkRowTransportTests(unittest.TestCase):
    def test_complete_row_matching_and_changed_row_refusal(self):
        digest='a'*64
        bits=[(1,index) for index in range(252)]
        records=[{'row':index,'a':[[2000+index,f'{1:064x}']],
                  'b':[[2000+index,f'{1:064x}']]} for index in range(252)]
        records.append({'row':999,'a':[[1504,f'{1:064x}']],
                        'b':[[1505,f'{1:064x}']]})
        extraction={'selected_rows':records,'templates':[
            {'row':index,'roles':[f'bit.{index}']} for index in range(252)]}
        chunks=[{'metadata':{'schema':'shieldd-transfer-ownership-v1',
                             'window_start':start,'window_count':min(16,126-start),
                             'relation_digest':digest,'domain_size':4096,'full_rows':1000},
                 'bits':bits,'derived':{handle:((2000+index,1),) for index,handle in enumerate(bits)}}
                for start in range(0,126,16)]
        cone={'rows':{999:(((1504,1),),((1505,1),))}}
        actual=copy.deepcopy(records)
        actual[-1]['a'][0][0]=1520;actual[-1]['b'][0][0]=1521
        def replay(stream,expected_relation,row_observer):
            self.assertEqual(expected_relation,digest)
            for row in actual:row_observer(row)
            return {'relation_digest':digest,'domain_size':4096,'stored_rows':1000}
        with patch.object(o,'join_chunks'),patch.object(o,'cone_certificates',return_value=cone),\
                patch.object(o,'quotient_certificates',return_value={'rows':{}}),\
                patch.object(o.relation,'inspect',side_effect=replay):
            result=o.extract_rnk_row_transport(chunks,[extraction]*8,None,digest)
            self.assertEqual(len(result['chunks']),8)
            self.assertEqual(result['chunks'][4]['blocks'][0][0]['a'][0][0],1520)
            actual[-1]['a'][0][1]=f'{2:064x}'
            with self.assertRaisesRegex(RelationError,'missing actual RNK transported arithmetic row'):
                o.extract_rnk_row_transport(chunks,[extraction]*8,None,digest)

class RnkInverseControlTests(unittest.TestCase):
    def test_local_assertion_omission_observes_identity(self):
        p=o.relation.MODULUS
        term=lambda column,value:[column,f'{value%p:064x}']
        checked={'metadata':{'constant_copy':5},'points':{'output':[('source',(1,7)),('source',(1,8))]},
                 'nonidentity_inverse':('source',(1,9)),
                 'derived':{(1,7):((10,1),),(1,8):((11,1),),(1,9):((12,1),)}}
        rows=[{'row':0,'a':[term(10,-1),term(12,1)],'b':[term(14,1)]},
              {'row':1,'a':[term(10,1),term(12,1)],'b':[term(13,4),term(14,1)]},
              {'row':2,'a':[term(5,1),term(13,-1)],'b':[]},
              {'row':3,'a':[term(0,1),term(5,-1)],'b':[]}]
        extracted={'products':[{'role':'nonidentity','rows':[0,1,2]}],'selected_rows':rows}
        with patch.object(o,'generate_rnk_inverse_boundary'):
            control=o.rnk_inverse_controls(checked,extracted)
            self.assertEqual(control['positive']['rejected_rows'],[])
            self.assertEqual(control['assertion_omission']['original_rejected_rows'],[2])
            self.assertTrue(control['assertion_omission']['point_is_identity'])
            rows[2]['a'][0]=term(5,2)
            with self.assertRaisesRegex(RelationError,'intended semantic omission not observed'):
                o.rnk_inverse_controls(checked,extracted)

if __name__=='__main__':unittest.main()
