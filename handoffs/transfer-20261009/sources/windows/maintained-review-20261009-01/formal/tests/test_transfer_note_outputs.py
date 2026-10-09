"""Actual output binding rows and receiver-only nonzero/range controls."""
import copy,io,json,unittest
from blake3 import blake3
from circuits import transfer_note_outputs as outputs,transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_note_spend import fixture as spend_fixture,encoded,source


def fixture(reverse_assertion=False):
    _,_,caller=spend_fixture();observed=dict(caller['observed']);records=[];required=set()
    def put(tag,index,lc=None):
        ref=source(tag,index);observed[(tag,index)]=canonical([(3+index,1)] if lc is None else lc);return ref
    def get(ref):required.add(tuple(ref['source']));return observed[tuple(ref['source'])]
    meta=caller['metadata']['caller'];pair=[];inverse=put(1,1200)
    payload=[put(2,2200+i,[(2200+i,1)]) for i in range(2)]
    for slot in range(2):
        address=[put(1,1300+i) for i in range(4)] if slot==0 else meta['address']
        note=[put(1,1400+3*slot),put(1,1401+3*slot),meta['asset'],*address,put(1,1402+3*slot)]
        output=dict(receiver=slot==0,note=note,amount_bits=[put(1,1500+256*slot+i)['source'] for i in range(128)],
            receiver_inverse=inverse if slot==0 else None,computed_commitment=put(2,2400+slot,[(2400+slot,1)]),
            commitment=put(1,1900+slot),capsule=[put(1,2000+7*slot+i) for i in range(7)],
            capsule_commitment=put(1,2100+slot),payload_key=payload)
        pair.append(output)
        for ref in [*note,output['computed_commitment'],output['commitment'],*output['capsule'],output['capsule_commitment'],*payload]:get(ref)
        if slot==0:get(inverse)
        required.update(tuple(bit) for bit in output['amount_bits'])
    copy,domain=4000,4096;outline=lambda lc:canonical((copy if c==0 else c,v) for c,v in lc)
    rows=[(canonical([(0,1),(copy,-1)]),())]
    for output in pair:
        rows.extend([(outline(combine(get(output['computed_commitment']),get(output['commitment']),-1)),()),
            (outline(combine(get(output['capsule_commitment']),get(output['note'][7]),-1)),())])
    a,b=get(inverse),get(pair[0]['note'][1]);aux,product=((3001,1),),((3000,1),)
    rows.extend([(outline(combine(a,b,-1)),aux),(outline(combine(a,b)),combine(aux,product,4)),
        (outline(combine(product,((0,1),),-1)),())])
    if reverse_assertion:
        rows[-1]=(canonical((c,-v) for c,v in rows[-1][0]),rows[-1][1])
    for output in pair:
        columns=[3+bit[1] for bit in output['amount_bits']]
        rows.extend([(((c,1),),((c,1),)) for c in columns])
        rows.append((combine(canonical((c,2**i) for i,c in enumerate(columns)),get(output['note'][1]),-1),()))
    for i,(a,b) in enumerate(rows):records.append(dict(row=i,a=[[c,f'{v:064x}'] for c,v in a],b=[[c,f'{v:064x}'] for c,v in b]))
    public,blocks=[[1,990]],[[1,991]];digest=blake3()
    digest.update(relation.NAMESPACE+relation.u64(domain)+relation.u64(len(rows))+relation.indices(public)+relation.u64(1)+relation.indices(blocks))
    for row in records:digest.update(b'A'+relation.terms(row['a'],domain)+b'B'+relation.terms(row['b'],domain))
    identity=dict(relation_digest=digest.hexdigest(),domain_size=domain,full_rows=len(rows),constant_copy=copy)
    caller['metadata'].update(identity)
    obj=dict(schema='shieldd-transfer-note-output-v1',family='transfer',scope=outputs.SCOPE,**identity,
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,outputs=pair,
        expressions=[dict(source=list(h),terms=[[c,f'{v:064x}'] for c,v in observed[h]]) for h in sorted(required)])
    header=dict(schema='shieldd-transfer-relation-v1',family='transfer',relation_digest=identity['relation_digest'],domain_size=domain,
        stored_rows=len(rows),public_inputs=1,committed_blocks=[1],constant_column=0,public_columns=[1],committed_columns=[[2]],
        source_public=public,source_blocks=[blocks],coefficient_encoding='canonical-big-endian-32',field_modulus=str(relation.MODULUS),
        role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',padding='implicit-all-zero-rows-to-domain-size')
    stream=io.BytesIO(b''.join(encoded(v) for v in [header,*records,dict(eof=True,rows=len(rows))]))
    return encoded(obj),caller,stream,rows


class NoteOutputTests(unittest.TestCase):
    def test_original_inverse_assertion_reverse_preserves_real_constructor(self):
        data,caller,stream,_=fixture(reverse_assertion=True)
        extracted=outputs.extract(data,stream,caller)
        plan=outputs.receiver_completion_plan(data,extracted,caller)
        self.assertTrue(plan['signed']);self.assertEqual(plan['writes'],[1203,3000,3001])
        sound=outputs.generate(data,extracted,caller)
        self.assertIn('rows [(0,1)] product normalized (by decide)).symm',sound)
        self.assertEqual(sound.count('#print axioms'),7)
        source=outputs.generate_receiver_completion(data,extracted,caller)
        self.assertIn('CompilerSignedCompletion.original_rows',source)
        self.assertEqual(source.count('#print axioms'),8)
        for amount in (1,19,2**128-1):
            base={column:(47*column+11)%relation.MODULUS for column in range(4096)}
            base[0]=base[4000]=1;base[1404]=amount
            rho=dict(base);rho[1203]=pow(amount,-1,relation.MODULUS)
            rho[3000]=1;rho[3001]=(rho[1203]-amount)**2 % relation.MODULUS
            evaluate=lambda lc:sum(rho[c]*v for c,v in lc)%relation.MODULUS
            self.assertTrue(all(evaluate(a)**2%relation.MODULUS==evaluate(b) for a,b in plan['raw'].values()))
            self.assertTrue(all(base[c]==rho[c] for c in base if c not in plan['writes']))
            rho[3000]=2
            self.assertFalse(all(evaluate(a)**2%relation.MODULUS==evaluate(b) for a,b in plan['raw'].values()))

    def test_receiver_completion_owns_only_three_actual_columns(self):
        data,caller,stream,_=fixture();selected=outputs.extract(data,stream,caller)
        plan=outputs.receiver_completion_plan(data,selected,caller);p=relation.MODULUS
        self.assertEqual(plan['writes'],[1203,3000,3001])
        self.assertEqual(len(plan['raw']),3)
        for amount in (1,19,2**128-1):
            base={c:(41*c+7)%p for c in range(4096)};base[0]=base[4000]=1
            base[1404]=amount;base[1407]=0
            rho=dict(base);rho[plan['quotient']]=pow(amount,-1,p)
            rho[plan['product']]=(1-sum(base[c]*v for c,v in plan['remainder']))%p
            rho[plan['auxiliary']]=(rho[plan['quotient']]-amount)**2%p
            evaluate=lambda lc:sum(rho[c]*v for c,v in lc)%p
            self.assertTrue(all(evaluate(a)**2%p==evaluate(b) for a,b in plan['raw'].values()))
            self.assertTrue(all(rho[c]==base[c] for c in base if c not in plan['writes']))
            self.assertEqual([rho[c] for c in (1,2,1404,1407)],
                             [base[c] for c in (1,2,1404,1407)])
            rho[plan['auxiliary']]=(rho[plan['auxiliary']]+1)%p
            self.assertFalse(all(evaluate(a)**2%p==evaluate(b) for a,b in plan['raw'].values()))
        sound_text=outputs.generate(data,selected,caller)
        self.assertIn('rows product [(0,1)] normalized (by decide)',sound_text)
        source_text=outputs.generate_receiver_completion(data,selected,caller)
        self.assertEqual(source_text.count('#print axioms'),8)
        self.assertIn('GroupRowCompletion.original_rows_complete',source_text)
        signature=source_text[source_text.index('theorem complete_receiver'):source_text.index(' :=',source_text.index('theorem complete_receiver'))]
        self.assertIn('legal : eval rho amount ≠ 0',signature)
        self.assertNotIn('(satisfied :',signature)
        self.assertNotIn('(inverseValue :',signature)
        changed=json.loads(data);old=changed['outputs'][1]['capsule'][0]['source']
        changed['outputs'][1]['capsule'][0]=changed['outputs'][0]['receiver_inverse']
        changed['expressions']=[entry for entry in changed['expressions'] if entry['source']!=old]
        changed=encoded(changed);stream.seek(0);extracted=outputs.extract(changed,stream,caller)
        with self.assertRaisesRegex(relation.RelationError,'inverse aliases readonly'):
            outputs.receiver_completion_plan(changed,extracted,caller)

    def test_actual_receiver_inverse_and_binding_rows_allow_zero_change(self):
        data,caller,stream,rows=fixture();selected=outputs.extract(data,stream,caller)
        certified=outputs.certificates(data,selected,caller);self.assertEqual(len(certified['raw']),8)
        checked=certified['checked'];p=relation.MODULUS;rho={c:0 for c in range(4096)};rho[0]=rho[4000]=1
        evaluate=lambda terms:sum(rho[c]*v for c,v in terms)%p
        for amount in (1,2**128-1):
            for slot,current in enumerate(checked['outputs']):
                value=amount if slot==0 else 0;rho[current['note'][1][0][0]]=value
                for i,c in enumerate(current['columns']):rho[c]=(value>>i)&1
                rho[current['computed'][0][0]]=37+slot;rho[current['commitment'][0][0]]=37+slot
                rho[current['capsule_commitment'][0][0]]=17+slot;rho[current['note'][7][0][0]]=17+slot
            rho[1203]=pow(amount,-1,p);rho[3000]=1;rho[3001]=(rho[1203]-amount)**2%p
            self.assertTrue(all(evaluate(a)**2%p==evaluate(b) for a,b in rows))
        rho[checked['outputs'][0]['note'][1][0][0]]=0
        self.assertFalse(all(evaluate(a)**2%p==evaluate(b) for a,b in rows))
        source_text=outputs.generate(data,selected,caller);self.assertEqual(source_text.count('#print axioms'),7)
        self.assertIn('Compiler.checked_product_sound',source_text)
        self.assertNotIn('change_nonzero',source_text);self.assertNotIn('actual_hash_sound',source_text)
        for slot in range(2):
            stream.seek(0);ranged=outputs.extract_range(data,stream,caller,slot)
            self.assertEqual(len(ranged['selected_rows']),130)
            range_source=outputs.generate_range(data,ranged,caller,slot)
            self.assertEqual(range_source.count('#print axioms'),5)
            self.assertIn('writeBits_range_complete',range_source)
            self.assertIn(f'namespace ShielddSecurity.RuntimeTransferOutput{slot}AmountRange',range_source)

    def test_source_policy_alias_row_omission_and_semantic_recovery_tamper_refuse(self):
        data,caller,stream,_=fixture();obj=json.loads(data);selected=outputs.extract(data,stream,caller)
        mutations=[lambda o:o['outputs'].reverse(),lambda o:o['outputs'][1].update(receiver_inverse=o['outputs'][0]['receiver_inverse']),
            lambda o:o['outputs'][0].update(receiver_inverse=None),lambda o:o['outputs'][1]['payload_key'].reverse(),
            lambda o:o['outputs'][0]['amount_bits'].reverse(),lambda o:o['outputs'][1]['note'].__setitem__(2,o['outputs'][1]['note'][1]),
            lambda o:o.update(repeated_observations_equal=False),lambda o:o['expressions'].pop()]
        for mutation in mutations:
            changed=copy.deepcopy(obj);mutation(changed)
            with self.assertRaises(relation.RelationError):outputs.inspect_metadata(encoded(changed),caller)
        for index in range(8):
            changed=copy.deepcopy(selected);changed['selected_rows'].pop(index)
            with self.assertRaises(relation.RelationError):outputs.certificates(data,changed,caller)
        changed=copy.deepcopy(selected);changed['selected_rows'][2]['a'][0][1]=f'{2:064x}'
        with self.assertRaisesRegex(relation.RelationError,'binding'):outputs.certificates(data,changed,caller)


if __name__=='__main__':unittest.main()
