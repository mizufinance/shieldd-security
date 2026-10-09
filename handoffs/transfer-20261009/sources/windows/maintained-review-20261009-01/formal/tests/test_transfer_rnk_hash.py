"""Sponge ingress controls; synthetic boundaries do not establish row semantics."""
import copy
import json
import unittest
from unittest.mock import patch
import contextlib
import io
import sys
from circuits import transfer_rnk_hash as h


def fixture():
    expressions = {}
    def ref(tag,index,lc=None):
        expressions[(tag,index)] = lc if lc is not None else [(3+index,1)]
        return {'source':[tag,index]}
    inputs = [ref(1,i) for i in range(9)]
    after0 = [ref(2,100+i,[(40+i,1)]) for i in range(6)]
    after1 = [ref(2,200+i,[(50+i,1)]) for i in range(6)]
    before0 = [{'native':f'{2321:064x}'}]+inputs[:5]
    before1 = [after0[0]]+[ref(2,300+i,[(41+i,1),(8+i,1)]) for i in range(4)]+[after0[5]]
    # Canonical column ordering is part of the serialized ingress contract.
    for x in expressions: expressions[x] = sorted(expressions[x])
    commit_after = [ref(2,400+i,[(60+i,1)]) for i in range(3)]
    hashes = [dict(domain=17,inputs=inputs,output=after1[1],blocks=[dict(before=before0,after=after0),dict(before=before1,after=after1)]),
              dict(domain=18,inputs=[after1[1]],output=commit_after[1],blocks=[dict(before=[{'native':f'{274:064x}'},after1[1],{'native':f'{0:064x}'}],after=commit_after)])]
    bindings = dict(inputs=inputs,hash=after1[1],commitment=commit_after[1],
                    regulated=ref(1,10),registered=ref(1,11),effective_nk=ref(2,500,[(70,1)]))
    handles = [[1,12],[1,13],[1,14],[2,600]]
    ref(1,12)
    obj = dict(schema='shieldd-transfer-rnk-hash-block-v1',family='transfer',scope=h.SCOPE,
               relation_digest='a'*64,domain_size=128,full_rows=100,constant_copy=127,
               ordinary_full_ordered_rows_equal=True,block=0,ivk_handles=handles,
               hashes=hashes,rnk_bindings=bindings,nodes=[],
               expressions=[dict(source=list(x),terms=[[c,f'{v:064x}'] for c,v in lc]) for x,lc in sorted(expressions.items())])
    return obj,handles,copy.deepcopy(bindings)


class BoundaryTests(unittest.TestCase):
    def check(self,obj,handles,bindings):
        return h.inspect_boundaries((json.dumps(obj)+'\n').encode(),'a'*64,handles,bindings)

    def test_all_absorptions_and_external_roles(self):
        obj,handles,bindings = fixture()
        self.assertEqual(self.check(obj,handles,bindings)['block'],0)
        changed = copy.deepcopy(obj)
        changed['hashes'][0]['blocks'][1]['before'][5] = changed['hashes'][0]['blocks'][0]['after'][4]
        with self.assertRaisesRegex(h.relation.RelationError,'wide absorption LC mismatch'):
            self.check(changed,handles,bindings)
        changed = copy.deepcopy(obj)
        changed['hashes'][1]['blocks'][0]['before'][0]['native'] = f'{275:064x}'
        with self.assertRaisesRegex(h.relation.RelationError,'commitment absorption/input mismatch'):
            self.check(changed,handles,bindings)
        changed = copy.deepcopy(obj)
        changed['rnk_bindings']['regulated'] = changed['rnk_bindings']['registered']
        with self.assertRaisesRegex(h.relation.RelationError,'accepted caller role mismatch'):
            self.check(changed,handles,bindings)

    def test_fail_closed_external_framing_and_hidden_cone(self):
        obj,handles,bindings = fixture()
        with self.assertRaisesRegex(h.relation.RelationError,'handle shape'):
            self.check(obj,[],bindings)
        with self.assertRaisesRegex(h.relation.RelationError,'exact RNK hash relation digest'):
            h.inspect_boundaries(b'{}\n','x',handles,bindings)
        with self.assertRaisesRegex(h.relation.RelationError,'missing RNK permutation node'):
            h.inspect_metadata((json.dumps(obj)+'\n').encode(),None,'a'*64,handles,bindings)

    def test_round_adapter_rejects_duplicate_physical_indices(self):
        state = dict(metadata_sha256='b'*64,block=0,
                     metadata=dict(domain_size=128,full_rows=100,constant_copy=127))
        row = dict(row=4,a=[[5,f'{1:064x}']],b=[])
        extracted = dict(metadata_sha256='b'*64,block=0,
                         identity=dict(relation_digest='a'*64,domain_size=128,stored_rows=100),
                         selected_rows=[row,copy.deepcopy(row)])
        with patch.object(h,'inspect_metadata',return_value=state):
            with self.assertRaisesRegex(h.relation.RelationError,'duplicate RNK selected row'):
                h.round_selection(b'',extracted,None,'a'*64,[],{})

    def test_control_harness_refuses_unrelated_rejection(self):
        obj,handles,bindings = fixture()
        obj['nodes'] = [dict(index=1,multiply=False,left=[0,0],right=[0,0])]
        state = dict(metadata=obj,block=0,metadata_sha256='b'*64)
        with patch.object(h,'inspect_metadata',side_effect=[state,h.relation.RelationError('truncated or empty row framing')]):
            with self.assertRaisesRegex(h.relation.RelationError,'unrelated RNK ingress refusal'):
                h.ingress_controls(b'',None,'a'*64,handles,bindings)

    def test_fifth_lane_json_roundtrip_and_active_coverage(self):
        original = {i:dict(kind='constant',coefficient=i) for i in range(6)}
        restored = json.loads(json.dumps(original))
        self.assertEqual(h.normalize_fifths(restored,6,0),original)
        self.assertEqual(h.normalize_fifths({'0':original[0]},6,4),{0:original[0]})
        for changed,reason in (({'00':original[0]},'noncanonical'),
                               ({False:original[0]},'noncanonical'),
                               ({0:original[0],'0':original[0]},'duplicate'),
                               ({'0':original[0]},'missing/extra')):
            with self.assertRaisesRegex(h.relation.RelationError,reason):
                h.normalize_fifths(changed,6,0)

    def test_joined_generator_substitutes_proved_dh_in_hash(self):
        source = h.generate_dh_sponge_join()
        self.assertIn('theorem actual_ivk_dh_hash', source)
        self.assertIn('rw [dh_input_values rho,dhRole] at hash', source)
        self.assertIn('[(model.coordinates (r • senderBase)).x', source)
        self.assertIn('RuntimeTransferRnkIvk.rawRows ++', source)
        self.assertIn('(RuntimeRnkInverse.rawRows ++ RuntimeRnkSponge.rawRows)', source)
        names = __import__('re').findall(r'#check @(\w+)', source)
        self.assertEqual(names, ['dh_input_columns','actual_dh_nonidentity','actual_ivk_dh',
                                'actual_hash_and_commitment','actual_regulated_branches',
                                'dh_input_values','actual_ivk_dh_hash'])

    def test_cli_requires_accepted_rnk_and_refuses_qualification(self):
        import security
        base=['check','--relation-export','unused','--expected-relation-digest','a'*64,
              '--rnk-hash-inspection','unused']
        for extra,reason in (([], 'requires matching RNK-DH inspection'),
                             (['--qualified-receipts','unused'],'cannot process qualification')):
            stderr=io.StringIO()
            with contextlib.redirect_stderr(stderr),patch.object(sys,'argv',['security.py',*base,*extra]):
                self.assertEqual(security.main(),1)
            self.assertIn(reason,stderr.getvalue())


if __name__ == '__main__':
    unittest.main()
