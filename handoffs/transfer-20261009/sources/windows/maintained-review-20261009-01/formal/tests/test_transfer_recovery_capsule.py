"""Recovery source joins, exact full-row extraction and owned writes."""
import copy, io, json, unittest
from blake3 import blake3
from circuits import transfer_recovery_capsule as recovery, transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine
from tests.test_transfer_note_outputs import fixture as output_fixture
from tests.test_transfer_note_spend import encoded, source


def fixture():
    output_data, caller, stream, rows = output_fixture()
    output = json.loads(output_data); required = set(); observed = {
        tuple(e['source']): tuple((c, int(v, 16)) for c, v in e['terms']) for e in output['expressions']}
    def put(column, lc=None):
        ref = source(1 if lc is None else 2, column-3 if lc is None else column)
        observed[tuple(ref['source'])] = canonical([(column, 1)] if lc is None else lc)
        return ref
    def value(ref):
        handle = tuple(ref['source']); required.add(handle); return observed[handle]
    capsules = []
    outline = lambda lc: canonical((4000 if c == 0 else c, v) for c, v in lc)
    for slot, out in enumerate(output['outputs']):
        base = 3700 + 30*slot
        cap = out['capsule']; amount = out['note'][1]; blinding = out['note'][0]
        entry = dict(payload_key=out['payload_key'], amount=amount, blinding=blinding,
            randomizer=put(base), bits=[put(3100+300*slot+i)['source'] for i in range(252)],
            seed=put(base+1), capsule=cap, commitment=out['capsule_commitment'],
            computed_epk=[put(base+2), put(base+3)], shared=[put(base+4), put(base+5)],
            secret=put(base+6), computed_confirmation=put(base+7),
            amount_stream=put(base+8), blinding_stream=put(base+9),
            epk_inverse=put(base+10), plaintext_inverse=put(base+11))
        entry['computed_c2'] = put(base+12, combine(value(entry['seed']), value(entry['secret'])))
        entry['computed_amount'] = put(base+13, combine(value(amount), value(entry['amount_stream'])))
        entry['computed_blinding'] = put(base+14, combine(value(blinding), value(entry['blinding_stream'])))
        for key, refs in entry.items():
            if key == 'bits': required.update(tuple(h) for h in refs)
            elif isinstance(refs, list):
                for ref in refs: value(ref)
            else: value(refs)
        pairs = list(zip((*entry['computed_epk'], entry['computed_c2'], entry['computed_confirmation'],
                         entry['computed_amount'], entry['computed_blinding']),
                         (cap[0], cap[1], cap[2], cap[4], cap[5], cap[6])))
        for i, (left, right) in enumerate(pairs):
            delta = combine(value(left), value(right), -1)
            # Exercise both allowed assertion orientations.
            rows.append((outline(canonical((c, -v) for c, v in delta) if i % 2 else delta), ()))
        for occurrence, key in enumerate(('epk_inverse', 'plaintext_inverse')):
            inverse, x = value(entry[key]), value(cap[0])
            product, aux = ((3800+4*slot+2*occurrence, 1),), ((3801+4*slot+2*occurrence, 1),)
            rows.extend([(outline(combine(inverse, x, -1)), aux),
                         (outline(combine(inverse, x)), combine(aux, product, 4)),
                         (outline(combine(product, ((0, 1),), -1)), ())])
        capsules.append(entry)
    records = [dict(row=i, a=[[c, f'{v:064x}'] for c, v in a], b=[[c, f'{v:064x}'] for c, v in b])
               for i, (a, b) in enumerate(rows)]
    header = json.loads(stream.readline()); digest = blake3()
    digest.update(relation.NAMESPACE+relation.u64(4096)+relation.u64(len(rows))+
                  relation.indices(header['source_public'])+relation.u64(1)+relation.indices(header['source_blocks'][0]))
    for row in records: digest.update(b'A'+relation.terms(row['a'],4096)+b'B'+relation.terms(row['b'],4096))
    identity = dict(relation_digest=digest.hexdigest(), domain_size=4096, full_rows=len(rows), constant_copy=4000)
    output.update(identity); caller['metadata'].update(identity)
    header.update(relation_digest=digest.hexdigest(), stored_rows=len(rows))
    metadata = dict(schema='shieldd-transfer-recovery-capsule-roles-v1', family='transfer', scope=recovery.SCOPE,
        **identity, ordinary_full_ordered_rows_equal=True, repeated_observations_equal=True, capsules=capsules,
        expressions=[dict(source=list(h), terms=[[c,f'{v:064x}'] for c,v in observed[h]]) for h in sorted(required)])
    stream_bytes=b''.join(encoded(v) for v in [header,*records,dict(eof=True,rows=len(rows))])
    return encoded(metadata), encoded(output), caller, stream_bytes


class RecoveryCapsuleTests(unittest.TestCase):
    def test_twelve_actual_assertions_construct_only_their_owned_target(self):
        data, outputs, caller, stream = fixture()
        selected = recovery.extract_bindings(data, io.BytesIO(stream), outputs, caller)
        cert = recovery.certificates(data, selected, outputs, caller)
        self.assertEqual(len(cert['raw']), 13)
        _,sound=recovery.generate_sound(data,selected,outputs,caller)
        self.assertEqual(sound.count('#print axioms'),13)
        self.assertEqual(sound.count('#check @'),13)
        self.assertEqual(sound.count('normalized (by decide)).symm'),6)
        p=relation.MODULUS
        for slot in (0,1):
            for role in recovery.ROLES:
                plan=recovery.completion_plan(data,selected,outputs,caller,slot,role)
                base={c:(37*c+19)%p for c in range(4096)}; base[0]=base[4000]=1
                rho=dict(base); rho[plan['target']]=sum(base[c]*v for c,v in plan['computed'])%p
                a,b=plan['raw_row']; evaluate=lambda lc:sum(rho[c]*v for c,v in lc)%p
                self.assertEqual(evaluate(a)**2%p,evaluate(b))
                self.assertTrue(all(rho[c]==base[c] for c in base if c!=plan['target']))
                _,source_text=recovery.generate_completion(data,selected,outputs,caller,slot,role)
                self.assertEqual(source_text.count('#print axioms'),6)
                self.assertIn('LinearBindingCompletion.original_complete',source_text)
                rho[plan['target']]=(rho[plan['target']]+1)%p
                self.assertNotEqual(evaluate(a)**2%p,evaluate(b))

    def test_four_distinct_inverse_triples_require_nonzero_epk(self):
        data,outputs,caller,stream=fixture()
        selected=recovery.extract_inverses(data,io.BytesIO(stream),outputs,caller)
        cert=recovery.inverse_certificates(data,selected,outputs,caller)
        self.assertEqual(len(cert['raw']),13); self.assertEqual(len(cert['inverses']),4)
        _,sound=recovery.generate_inverse_sound(data,selected,outputs,caller)
        self.assertEqual(sound.count('#print axioms'),9)
        self.assertEqual(sound.count('#check @'),9)
        p=relation.MODULUS;rho={c:0 for c in range(4096)};rho[0]=rho[4000]=1
        for slot,occurrence,item in cert['inverses']:
            plan=recovery.inverse_completion_plan(data,selected,outputs,caller,slot,occurrence)
            self.assertEqual(len(plan['writes']),3)
            _,ctor=recovery.generate_inverse_completion(data,selected,outputs,caller,slot,occurrence)
            self.assertEqual(ctor.count('#print axioms'),8)
            signature=ctor[ctor.index('theorem complete_inverse'):ctor.index(' :=',ctor.index('theorem complete_inverse'))]
            self.assertIn('legal : eval rho epkX ≠ 0',signature)
            self.assertNotIn('satisfied :',signature)
            base={c:(19*c+23)%p for c in range(4096)};base[0]=base[4000]=1
            base[item['denominator'][0][0]]=31+slot
            local=dict(base);local[plan['quotient']]=pow(base[item['denominator'][0][0]],-1,p)
            local[plan['product']]=(1-sum(base[c]*v for c,v in plan['remainder']))%p
            local[plan['auxiliary']]=(local[plan['quotient']]-base[item['denominator'][0][0]])**2%p
            ev=lambda lc:sum(local[c]*v for c,v in lc)%p
            self.assertTrue(all(ev(a)**2%p==ev(b) for a,b in plan['raw'].values()))
            self.assertTrue(all(local[c]==base[c] for c in base if c not in plan['writes']))
            x=item['denominator'][0][0];q=item['quotient'][0][0]
            rho[x]=17+slot;rho[q]=pow(rho[x],-1,p)
            rho[item['output'][0][0]]=1;rho[item['auxiliary'][0][0]]=(rho[q]-rho[x])**2%p
        evaluate=lambda lc:sum(rho[c]*v for c,v in lc)%p
        self.assertTrue(all(evaluate(a)**2%p==evaluate(b) for a,b in cert['raw'].values()))
        rho[cert['inverses'][0][2]['denominator'][0][0]]=0
        self.assertFalse(all(evaluate(a)**2%p==evaluate(b) for a,b in cert['raw'].values()))
        for index in range(1,13):
            changed=copy.deepcopy(selected);changed['selected_rows'].pop(index)
            with self.assertRaises(relation.RelationError):recovery.inverse_certificates(data,changed,outputs,caller)

    def test_scope_role_lc_private_alias_and_full_stream_controls(self):
        data,outputs,caller,stream=fixture();obj=json.loads(data)
        mutations=[lambda o:o.update(repeated_observations_equal=False), lambda o:o['capsules'].reverse(),
            lambda o:o['capsules'][0].update(amount=o['capsules'][0]['blinding']),
            lambda o:o['capsules'][0]['bits'].reverse(),lambda o:o['expressions'].pop(),
            lambda o:o['capsules'][0].update(plaintext_inverse=o['capsules'][0]['epk_inverse'])]
        for mutate in mutations:
            changed=copy.deepcopy(obj);mutate(changed)
            with self.assertRaises(relation.RelationError):recovery.inspect_metadata(encoded(changed),outputs,caller)
        changed=copy.deepcopy(obj)
        handle=changed['capsules'][0]['computed_c2']['source']
        next(e for e in changed['expressions'] if e['source']==handle)['terms'][0][1]=f'{2:064x}'
        with self.assertRaisesRegex(relation.RelationError,'addition LC'):recovery.inspect_metadata(encoded(changed),outputs,caller)
        broken=bytearray(stream);pos=broken.find(b'0000000000000000000000000000000000000000000000000000000000000001')
        broken[pos+63]=ord('2')
        with self.assertRaises(relation.RelationError):recovery.extract_bindings(data,io.BytesIO(broken),outputs,caller)


if __name__=='__main__':unittest.main()
