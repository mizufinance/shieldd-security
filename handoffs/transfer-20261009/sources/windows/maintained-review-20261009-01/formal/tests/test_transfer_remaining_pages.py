"""Tiny synthetic schemas only; no fixture is a capture or ordinary proof."""
import copy
import json
import unittest
from unittest.mock import patch
from blake3 import blake3
from circuits import transfer_remaining_pages as pages
from circuits.transfer_relation import RelationError


def encoded(obj): return (json.dumps(obj, separators=(',', ':')) + '\n').encode()


def fixture():
    ref = {'source': [1, 0]}
    records = []
    next_bit = 100
    for (scope, tag, ordinal), width in pages.shapes().items():
        values = [copy.deepcopy(ref) for _ in range(width)]
        if tag.endswith('-bits'):
            values = [{'source': [1, next_bit + i]} for i in range(width)]
            next_bit += width
        records.append(dict(scope=scope, tag=tag, ordinal=ordinal, values=values))
    at = lambda scope, tag: next(r['values'] for r in records if (r['scope'], r['tag'], r['ordinal']) == (scope, tag, 0))
    published = at('encryption', 'published44')
    for j, index in enumerate([*range(26, 31), *range(31, 36)]): published[index] = {'source': [1, 10000+j]}
    at('encryption', 'audit-output')[:] = published[26:31] + [published[35]]
    endpoints = at('encryption', 'metadata-equality-endpoints')
    endpoints[:] = sum(([published[26+i], copy.deepcopy(ref)] for i in range(5)), []) + [published[35], copy.deepcopy(ref)] + sum(([published[31+i], copy.deepcopy(ref)] for i in range(4)), [])
    calls = []
    for scope in pages.CALL_ORDER:
        for domain, arity in pages.roster(scope):
            width, rate = (3, 2) if arity <= 2 else (6, 5)
            calls.append(dict(scope=scope, domain=domain, inputs=[copy.deepcopy(ref) for _ in range(arity)],
                              output=copy.deepcopy(ref), blocks=[dict(before=[copy.deepcopy(ref) for _ in range(width)], after=[copy.deepcopy(ref) for _ in range(width)]) for _ in range((arity+rate-1)//rate)]))
    for scope in ('sender', 'receiver'):
        hs = [h for h in calls if h['scope'] == scope]
        for level in range(16): hs[level+1]['inputs'][0] = {'native': f'{level+1:064x}'}
    hs = [h for h in calls if h['scope'] == 'volume']
    for level in range(24): hs[level+2]['inputs'][0] = {'native': f'{level+1:064x}'}
    fields = [copy.deepcopy(ref) for _ in range(64)]
    fields[47:51] = published[26:30]
    fields[51:55] = published[31:35]
    fields[55] = published[35]
    at('statement', 'ordered64')[:] = fields
    calls[-1]['inputs'] = copy.deepcopy(fields)
    scope = 'encryption'
    handles = sorted({tuple(v['source']) for r in records if r['scope'] in ('caller', scope) for v in r['values'] if 'source' in v})
    expressions = [dict(source=list(h), terms=[[3+h[1], f'{1:064x}']]) for h in handles]
    page = dict(schema='shieldd-transfer-remaining-source-page-v1', family='transfer', scope=scope, ordinal=0,
                qualification=False, ordinary_full_ordered_rows_equal=False, repeated_observations_equal=False,
                records=records, calls=calls, hash=None, nodes=[], expressions=expressions)
    data = encoded(page)
    descriptors = [dict(ordinal=i, suffix=f'pending-page-{i:03}.json', bytes=len(data) if i == 0 else 1,
                        blake3=blake3(data).hexdigest() if i == 0 else '00'*32, hash=h, block=b)
                   for i, (h, b) in enumerate(pages.descriptors(scope))]
    identity = dict(relation_digest='ab'*32, domain_size=262144, full_rows=200770, constant_copy=200692)
    manifest = dict(schema='shieldd-transfer-remaining-source-pages-v1', family='transfer', scope=scope,
                    pages=descriptors, qualification=False, semantic_status=pages.STATUS,
                    ordinary_full_ordered_rows_equal=True, repeated_observations_equal=True, **identity)
    accepted = dict(metadata={**identity, 'caller':dict(address=[copy.deepcopy(ref)]*4, asset=copy.deepcopy(ref),
                                                     regulated=copy.deepcopy(ref), nk=copy.deepcopy(ref), effective_nk=copy.deepcopy(ref), ak=[copy.deepcopy(ref)]*2)},
                    observed={}, metadata_sha256='cd'*32)
    return manifest, page, accepted


def inspect(manifest, page, accepted):
    data = encoded(page)
    manifest = copy.deepcopy(manifest)
    manifest['pages'][0]['bytes'] = len(data)
    manifest['pages'][0]['blake3'] = blake3(data).hexdigest()
    return pages.inspect_page(encoded(manifest), data, 0, accepted)


def tree_fixture():
    """Finite synthetic row templates; never a qualified runtime observation."""
    m, p, a = fixture(); p['scope'] = m['scope'] = 'sender'
    at = lambda tag, ordinal=0: next(r['values'] for r in p['records']
                                     if (r['scope'], r['tag'], r['ordinal']) == ('sender', tag, ordinal))
    tree = [{'source': [1, 60000+i]} for i in range(14)]
    at('tree-level')[:] = tree
    member = at('membership'); member[:2] = [tree[0], tree[13]]
    hs = [h for h in p['calls'] if h['scope'] == 'sender']
    hs[0]['output'] = hs[0]['blocks'][-1]['after'][1] = tree[0]
    hs[1]['inputs'][1:] = tree[8:12]
    hs[1]['output'] = hs[1]['blocks'][-1]['after'][1] = tree[12]
    at('tree-level', 1)[0] = tree[12]
    for i in range(1, 16): at('tree-level', i)[13] = tree[13]
    handles = sorted({tuple(v['source']) for r in p['records'] if r['scope'] in ('caller', 'sender')
                      for v in r['values'] if 'source' in v})
    p['expressions'] = [dict(source=list(h), terms=[[h[1]+3, f'{1:064x}']]) for h in handles]
    payload = encoded(p)
    m['pages'] = [dict(ordinal=i, suffix=f'pending-page-{i:03}.json', bytes=len(payload) if i == 0 else 1,
                      blake3=blake3(payload).hexdigest() if i == 0 else '00'*32, hash=h, block=b)
                  for i, (h, b) in enumerate(pages.descriptors('sender'))]
    checked = pages.tree_level_obligations(encoded(m), payload, 0, a)
    copy_col = m['constant_copy']
    outline = lambda lc: pages.canonical((copy_col if c == 0 else c, v) for c, v in lc)
    physical = [(pages.canonical([(0, 1), (copy_col, -1)]), ())]
    physical += [(outline(bit), outline(bit)) for bit in checked['values'][1:3]]
    for i, (_, left, right, output) in enumerate(checked['products']):
        auxiliary = ((70000+i, 1),)
        physical += [(outline(pages.combine(left, right, -1)), auxiliary),
                     (outline(pages.combine(left, right)), outline(pages.combine(auxiliary, output, 4)))]
    selected = [dict(row=i, a=[[c, f'{v:064x}'] for c,v in left], b=[[c, f'{v:064x}'] for c,v in right])
                for i,(left,right) in enumerate(physical)]
    extracted = dict(metadata_sha256=checked['checked']['metadata_sha256'], tree_level=0, tree_scope='sender',
                     identity=dict(relation_digest=m['relation_digest'], domain_size=m['domain_size'], stored_rows=m['full_rows']),
                     selected_rows=selected)
    return m, p, a, extracted


def tree_position_fixture():
    """Synthetic 32-bit ordered assertion; not a runtime capture or replay."""
    m, p, a, _ = tree_fixture()
    for record in p['records']:
        if record['scope'] == 'sender' and record['tag'] == 'tree-level':
            i = record['ordinal']
            record['values'][1:3] = [{'source': [1, 61000+2*i+j]} for j in range(2)]
    handles = sorted({tuple(v['source']) for r in p['records'] if r['scope'] in ('caller', 'sender')
                      for v in r['values'] if 'source' in v})
    p['expressions'] = [dict(source=list(h), terms=[[3+h[1], f'{1:064x}']]) for h in handles]
    payload = encoded(p); m['pages'][0].update(bytes=len(payload), blake3=blake3(payload).hexdigest())
    selected = pages.tree_position_obligations(encoded(m), payload, a)
    copy_col = m['constant_copy']
    raw = [(pages.canonical([(0, 1), (copy_col, -1)]), ())]
    raw += [(bit, bit) for bit in selected['bits']]
    raw += [(selected['delta'], ())]
    extracted = dict(metadata_sha256=selected['checked']['metadata_sha256'], tree_scope='sender',
        identity=dict(relation_digest=m['relation_digest'], domain_size=m['domain_size'], stored_rows=m['full_rows']),
        selected_rows=[dict(row=i, a=[[c, f'{v:064x}'] for c,v in left],
                           b=[[c, f'{v:064x}'] for c,v in right]) for i,(left,right) in enumerate(raw)])
    return m, p, a, extracted


def membership_fixture():
    """Synthetic materialized product+zero assertion; not a runtime capture."""
    m,p,a,_=tree_fixture()
    root={'source':[1,62000]}
    for r in p['records']:
        if r['scope']=='sender' and r['tag']=='computed-root':r['values'][0]=root
        if r['scope']=='sender' and r['tag']=='tree-level' and r['ordinal']==15:r['values'][12]=root
    hs=[h for h in p['calls']if h['scope']=='sender']
    hs[-1]['output']=hs[-1]['blocks'][-1]['after'][1]=root
    handles=sorted({tuple(v['source'])for r in p['records']if r['scope']in('caller','sender')for v in r['values']if'source'in v})
    p['expressions']=[dict(source=list(h),terms=[[3+h[1],f'{1:064x}']])for h in handles]
    data=encoded(p);m['pages'][0].update(bytes=len(data),blake3=blake3(data).hexdigest())
    selected=pages.membership_obligations(encoded(m),data,a)
    left,right=selected['regulated'],selected['difference'];auxiliary=((71000,1),);output=((71001,1),)
    physical=[(pages.canonical([(0,1),(m['constant_copy'],-1)]),()),(left,left),
              (pages.combine(left,right,-1),auxiliary),
              (pages.combine(left,right),pages.combine(auxiliary,output,4)),(output,())]
    x=dict(metadata_sha256=selected['checked']['metadata_sha256'],membership_scope='sender',
      identity=dict(relation_digest=m['relation_digest'],domain_size=m['domain_size'],stored_rows=m['full_rows']),
      selected_rows=[dict(row=i,a=[[c,f'{v:064x}']for c,v in aa],b=[[c,f'{v:064x}']for c,v in bb])for i,(aa,bb)in enumerate(physical)])
    return m,p,a,x


class RemainingPagesTests(unittest.TestCase):
    def test_actual_membership_gate_keeps_materialization_and_zero_assertion(self):
        m,p,a,x=membership_fixture()
        selected=pages.membership_certificates(encoded(m),encoded(p),x,a)
        self.assertEqual(selected['output'],((71001,1),))
        source=pages.generate_membership(encoded(m),encoded(p),x,a)
        self.assertIn('ScalarRows.checked_product_sound',source)
        self.assertIn('Compiler.checked_assertion_sound',source)
        self.assertIn('active : eval rho regulated ≠ 0',source)
        self.assertEqual(source.count('#print axioms'),5)

    def test_membership_missing_assertion_changed_product_and_scope_refused(self):
        for kind in ('assertion','product','scope'):
            m,p,a,x=membership_fixture()
            if kind=='assertion':x['selected_rows'].pop()
            elif kind=='product':x['selected_rows'][-2]['b'][-1][1]=f'{8:064x}'
            else:x['membership_scope']='receiver'
            with self.assertRaises(RelationError):pages.generate_membership(encoded(m),encoded(p),x,a)

    def test_volume_exact_prior_successor_previous_and_padding_arguments(self):
        for index, lane in ((1, 2), (26, 1), (27, 2), (28, 2), (29, 1), (30, 2)):
            m, p, a = fixture()
            calls = [h for h in p['calls'] if h['scope'] == 'volume']
            calls[index]['inputs'][lane] = {'native': f'{42:064x}'}
            with self.assertRaisesRegex(RelationError, 'volume exact'):
                inspect(m, p, a)

    def test_position_ordered_bits_and_assertion_generate_bound(self):
        m, p, a, extracted = tree_position_fixture()
        source = pages.generate_tree_position(encoded(m), encoded(p), extracted, a)
        self.assertIn('range_sound', source)
        self.assertIn('n < 2^32', source)
        self.assertIn('fieldBinary (bits.map rho) = eval rho position', source)
        self.assertEqual(source.count('#print axioms'), 4)
        self.assertNotIn('positionMeaning', source)

    def test_position_changed_assertion_bit_alias_and_unused_row_refused(self):
        for kind in ('assertion', 'alias', 'extra', 'scope'):
            m, p, a, extracted = tree_position_fixture()
            if kind == 'assertion': extracted['selected_rows'][-1]['a'][0][0] += 1
            elif kind == 'alias':
                records = [r for r in p['records'] if r['scope']=='sender' and r['tag']=='tree-level']
                records[1]['values'][1] = records[0]['values'][1]
                payload=encoded(p);m['pages'][0].update(bytes=len(payload),blake3=blake3(payload).hexdigest())
            elif kind == 'extra':
                row=copy.deepcopy(extracted['selected_rows'][-1]);row['row']+=1;extracted['selected_rows'].append(row)
            else: extracted['tree_scope']='receiver'
            with self.assertRaises(RelationError):
                pages.generate_tree_position(encoded(m), encoded(p), extracted, a)

    def test_tree_generator_derives_ordered_children_from_actual_templates(self):
        m, p, a, extracted = tree_fixture()
        source = pages.generate_tree_level(encoded(m), encoded(p), 0, extracted, a)
        self.assertIn('Tree.wiring_sound', source)
        self.assertIn('ScalarRows.checked_product_sound', source)
        self.assertIn('Compiler.checked_row_sound', source)
        self.assertIn('theorem actual_children', source)
        self.assertEqual(source.count('#print axioms'), 9)
        self.assertNotIn('lowBoolean :', source.split('theorem actual_children')[1].split(':= by')[0])
        self.assertNotIn('desired', source)
        # No ordinary row stream has been replayed; these are synthetic source checks.

    def test_tree_wrong_level_product_boolean_and_extra_row_refused(self):
        for kind in ('level', 'product', 'Boolean', 'extra'):
            m, p, a, extracted = tree_fixture()
            if kind == 'level': extracted['tree_level'] = True
            elif kind == 'product': extracted['selected_rows'][-1]['b'][0][0] += 1
            elif kind == 'Boolean': extracted['selected_rows'][1]['b'][0][0] += 1
            else:
                row = copy.deepcopy(extracted['selected_rows'][-1]); row['row'] += 1
                extracted['selected_rows'].append(row)
            with self.assertRaises(RelationError): pages.generate_tree_level(encoded(m), encoded(p), 0, extracted, a)

    def test_tree_extractor_requests_boolean_and_six_real_products(self):
        m, p, a, _ = tree_fixture()
        with patch.object(pages.arithmetic, 'extract_templates', return_value={}) as matcher:
            pages.extract_tree_level(encoded(m), encoded(p), 0, object(), a)
        self.assertEqual(len(matcher.call_args.args[4]), 3)
        self.assertEqual(len(matcher.call_args.args[5]), 6)
        self.assertEqual(matcher.call_args.args[6], [])
        self.assertTrue(all(output is not None and numerator is None
                            for _, _, _, output, numerator in matcher.call_args.args[5]))

    def test_exact_roles_and_separate_metadata_endpoints(self):
        m, p, a = fixture()
        checked = inspect(m, p, a)
        endpoints = checked['records']['encryption', 'metadata-equality-endpoints', 0]
        self.assertNotEqual(endpoints[0], endpoints[1])
        self.assertEqual(len(checked['records']), 110)

    def test_pending_manifest_and_premature_page_flags_refused(self):
        for target in ('manifest', 'page'):
            m, p, a = fixture()
            if target == 'manifest': m['repeated_observations_equal'] = False
            else: p['ordinary_full_ordered_rows_equal'] = True
            with self.assertRaises(RelationError): inspect(m, p, a)

    def test_wrong_output_amount_slot_refused_even_with_fresh_page_digest(self):
        m, p, a = fixture()
        next(r for r in p['records'] if (r['scope'], r['tag']) == ('routing', 'shared'))['values'][1] = {'source':[1, 999]}
        with self.assertRaisesRegex(RelationError, 'routing exact change slot'): inspect(m, p, a)

    def test_wrong_ordered64_field_and_wrong_hash_domain_refused(self):
        for kind in ('field', 'domain'):
            m, p, a = fixture()
            if kind == 'field': next(r for r in p['records'] if r['tag'] == 'ordered64')['values'][3] = {'source':[1, 888]}
            else: p['calls'][-1]['domain'] = 35
            with self.assertRaises(RelationError): inspect(m, p, a)

    def test_distinct_bit_alias_and_missing_record_refused(self):
        for kind in ('bits', 'record'):
            m, p, a = fixture()
            if kind == 'bits':
                values = next(r for r in p['records'] if r['tag'] == 'timestamp-bits')['values']; values[1] = values[0]
            else: p['records'].pop()
            with self.assertRaises(RelationError): inspect(m, p, a)

    def test_changed_witness_lc_and_boolean_descriptor_refused(self):
        for kind in ('lc', 'descriptor'):
            m, p, a = fixture()
            if kind == 'lc': p['expressions'][0]['terms'][0][0] += 1
            else: m['pages'][0]['ordinal'] = False
            with self.assertRaises(RelationError): inspect(m, p, a)

    def test_metadata_extraction_requires_ten_actual_row_templates(self):
        m, p, a = fixture(); data = encoded(p)
        with patch.object(pages.arithmetic, 'extract_templates', return_value={'identity':{}}) as extract:
            pages.extract_metadata_equalities(encoded(m), data, object(), a)
        self.assertEqual(len(extract.call_args.args[4]), 11)
        self.assertEqual(extract.call_args.args[5:7], ([], []))
        self.assertTrue(all(rhs == () for _, rhs in extract.call_args.args[4]))
        # This mocks a matcher, not a successful full stream replay.

    def test_exact_descriptors_cover120pages112permutations(self):
        self.assertEqual(sum(len(pages.descriptors(s)) for s in pages.SCOPES), 120)
        self.assertEqual(sum(len(pages.roster(s)) for s in pages.SCOPES), 98)
        self.assertEqual(len(pages.shapes()), 110)

    def test_binding_generator_requires_selected_rows_and_no_desired_equality_premise(self):
        m, p, a = fixture()
        data = encoded(p); checked = inspect(m, p, a)
        endpoints = checked['records']['encryption', 'metadata-equality-endpoints', 0]
        pairs = [(((0, 1), (200692, -1 % pages.relation.MODULUS)), ())]
        for i in range(10):
            left = checked['observed'][tuple(endpoints[2*i]['source'])]
            right = checked['observed'][tuple(endpoints[2*i+1]['source'])]
            pairs.append((pages.combine(left, right, -1), ()))
        selected = [dict(row=i, a=[[c, f'{v:064x}'] for c, v in x], b=[[c, f'{v:064x}'] for c, v in y]) for i, (x, y) in enumerate(pairs)]
        extracted = dict(metadata_sha256=checked['metadata_sha256'], selected_rows=selected,
                         identity=dict(relation_digest=m['relation_digest'], domain_size=m['domain_size'], stored_rows=m['full_rows']))
        source = pages.generate_metadata_bindings(encoded(m), data, extracted, a)
        self.assertIn('theorem timestamp_binding', source)
        self.assertIn('Compiler.checked_assertion_sound', source)
        self.assertEqual(source.count('satisfied : Satisfies rho rawRows'), 10)
        bad = copy.deepcopy(extracted); bad['selected_rows'][-1]['a'][0][0] += 1
        with self.assertRaises(RelationError): pages.generate_metadata_bindings(encoded(m), data, bad, a)
        # These finite synthetic rows have not been replayed as an ordinary runtime.


if __name__ == '__main__': unittest.main()
