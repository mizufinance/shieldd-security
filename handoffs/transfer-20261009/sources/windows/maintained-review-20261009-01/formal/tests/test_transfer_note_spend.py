"""Typed synthetic current-spend lowering tests; no actual capture qualification."""
import copy
import io
import json
import unittest
from blake3 import blake3
from circuits import transfer_note_spend as notes, transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine
from tests import test_transfer_authorization_roles as caller_fixture


def encoded(obj): return (json.dumps(obj)+'\n').encode()
def source(tag,index): return {'source':[tag,index]}


def fixture(rows=None, swapped=False, fused=False, ambiguous=False, nonunit=False):
    typed = caller_fixture.AuthorizationRoleTests(); typed.setUp()
    accepted = typed.parse(); caller = accepted['metadata']['caller']; auth = accepted['metadata']['spend']
    observed = dict(accepted['observed']); shared = dict(asset=caller['asset'],address=caller['address'],
        nk=caller['effective_nk'],randomizer=auth['randomizer'],anchor=source(1,500))
    w = lambda index: source(1,index)
    n = lambda index: source(2,index)
    def put(v,lc=None):
        handle = tuple(v['source'])
        observed[handle] = canonical(lc if lc is not None else [(3+handle[1],1)])
        return v
    put(shared['anchor'])
    spends = []
    for slot in range(2):
        base = 501+5*slot
        spend = dict(shared=copy.deepcopy(shared),note=[put(w(base)),put(w(base+1)),shared['asset'],
            *shared['address'],put(w(base+2))],commitment=put(n(40+3*slot),[(960+3*slot,1)]),
            position=put(w(base+3)),real_nullifier=put(n(41+3*slot),[(961+3*slot,1)]),
            computed_anchor=put(n(42+3*slot),[(962+3*slot,1)]),nullifier=put(w(512+slot)),
            amount_bits=[],position_bits=[],dummy={'native':f'{0:064x}'},optional=None)
        for name,start,size in (('amount_bits',600+176*slot,128),('position_bits',728+176*slot,48)):
            spend[name] = [put(w(i))['source'] for i in range(start,start+size)]
        spends.append(spend)
    second = spends[1]; bit = put(w(510)); seed = put(w(511)); synthetic = put(n(46),[(966,1)])
    get = lambda v: observed[tuple(v['source'])]
    delta = put(n(47),combine(get(synthetic),get(second['real_nullifier']),-1))
    def output(index):
        return [(967+index,2 if nonunit and index==0 else 1)]+([(8,3+index)] if fused else [])+([(978,1)] if ambiguous and index==0 else [])
    selector_product = put(n(48),output(0))
    selected = put(n(49),combine(get(second['real_nullifier']),get(selector_product)))
    real = put(n(50),combine(((0,1),),get(bit),-1))
    anchor_delta = put(n(51),combine(get(second['computed_anchor']),get(shared['anchor']),-1))
    anchor_product = put(n(52),output(1)); amount_product = put(n(53),output(2))
    products = [[bit,delta,selector_product],[real,anchor_delta,anchor_product],[bit,second['note'][1],amount_product]]
    second.update(dummy=bit,optional=dict(domain=22,slot=1,seed=seed,synthetic=synthetic,selected=selected,products=products))
    required = set()
    def collect(v):
        if isinstance(v,dict):
            if set(v)=={'source'}: required.add(tuple(v['source']))
            else:
                for x in v.values(): collect(x)
        elif isinstance(v,list):
            for x in v: collect(x)
    collect(spends)
    required.update(tuple(b) for s in spends for key in ('amount_bits','position_bits') for b in s[key])
    obj = dict(schema='shieldd-transfer-note-spend-v1',family='transfer',scope=notes.SCOPE,
        relation_digest='a'*64,domain_size=1024,full_rows=13,constant_copy=1000,
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,spends=spends,
        expressions=[dict(source=list(h),terms=[[c,f'{v:064x}'] for c,v in observed[h]]) for h in sorted(required)],
        nodes=[dict(index=p[2]['source'][1],multiply=True,left=p[0]['source'],right=p[1]['source']) for p in products])
    if rows is None:
        pairs = [(canonical([(0,1),(1000,-1)]),())]
        outline = lambda lc: canonical((1000 if c==0 else c,v) for c,v in lc)
        assertion = lambda left,right=(): pairs.append((outline(combine(left,right,-1)),()))
        assertion(get(spends[0]['real_nullifier']),get(spends[0]['nullifier']))
        assertion(get(spends[0]['computed_anchor']),get(shared['anchor']))
        pairs.append((get(bit),get(bit)))
        assertion(get(selected),get(second['nullifier']))
        for index,p in enumerate(products):
            left,right,out = map(get,p); auxiliary=((975+index,1),)
            difference=combine(left,right,-1)
            if swapped: difference=canonical((c,-v) for c,v in difference)
            pairs.extend([(outline(difference),auxiliary),(outline(combine(left,right)),combine(auxiliary,out,4))])
            if index: assertion(out)
        rows = [dict(row=index,a=[[c,f'{v:064x}'] for c,v in a],b=[[c,f'{v:064x}'] for c,v in b])
                for index,(a,b) in enumerate(pairs)]
    digest = blake3(); public=[[1,990]]; blocks=[[1,991]]
    digest.update(relation.NAMESPACE+relation.u64(1024)+relation.u64(len(rows))+
                  relation.indices(public)+relation.u64(1)+relation.indices(blocks))
    for row in rows: digest.update(b'A'+relation.terms(row['a'],1024)+b'B'+relation.terms(row['b'],1024))
    value=digest.hexdigest(); obj.update(relation_digest=value,full_rows=len(rows))
    accepted['metadata'].update(relation_digest=value,full_rows=len(rows))
    header = dict(schema='shieldd-transfer-relation-v1',family='transfer',relation_digest=value,
        domain_size=1024,stored_rows=len(rows),public_inputs=1,committed_blocks=[1],constant_column=0,
        public_columns=[1],committed_columns=[[2]],source_public=public,source_blocks=[blocks],
        coefficient_encoding='canonical-big-endian-32',field_modulus=str(relation.MODULUS),
        role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',
        padding='implicit-all-zero-rows-to-domain-size')
    stream=io.BytesIO(b''.join(encoded(v) for v in [header,*rows,dict(eof=True,rows=len(rows))]))
    return encoded(obj),stream,accepted


class NoteSpendTests(unittest.TestCase):
    def test_two_notes_actual_templates_and_generated_audits(self):
        args=fixture(); result=notes.extract(*args)
        certs=notes.certificates(args[0],result,args[2])
        self.assertEqual(len(certs['rows']),13)
        self.assertEqual([certs['certificates']['product.'+n]['auxiliary'] for n in ('selector','anchor','amount')],
                         [((975,1),),((976,1),),((977,1),)])
        source_text=notes.generate(args[0],json.loads(json.dumps(result)),args[2])
        self.assertEqual(source_text.count('#print axioms'),7)
        self.assertIn('theorem both_spend_branches',source_text)
        self.assertIn('Compiler.checked_product_sound',source_text)
        self.assertNotIn('(selected :',source_text)

    def test_swapped_minus_square_is_recovered(self):
        args=fixture(swapped=True); result=notes.extract(*args)
        certs=notes.certificates(args[0],result,args[2])['certificates']
        self.assertTrue(all(certs['product.'+n]['swapped'] for n in ('selector','anchor','amount')))
        self.assertIn('theorem optional_branch',notes.generate(args[0],result,args[2]))

    def test_every_missing_semantic_row_is_refused_after_reframing_digest(self):
        args=fixture(); baseline=notes.extract(*args)['selected_rows']
        for omitted in range(13):
            rows=copy.deepcopy(baseline); rows.pop(omitted)
            for index,row in enumerate(rows):row['row']=index
            with self.subTest(omitted=omitted),self.assertRaisesRegex(relation.RelationError,'missing note-spend'):
                notes.extract(*fixture(rows=rows))

    def test_closed_roles_source_dag_and_pending_refusals(self):
        data,stream,accepted=fixture(); base=json.loads(data)
        mutations = {
            'history':lambda o:o['spends'][1].update(history=source(1,511)),
            'order':lambda o:o['spends'].reverse(),
            'domain':lambda o:o['spends'][1]['optional'].update(domain=23),
            'slot':lambda o:o['spends'][1]['optional'].update(slot=True),
            'ordinary-pending':lambda o:o.update(ordinary_full_ordered_rows_equal=False),
            'repeat-pending':lambda o:o.update(repeated_observations_equal=False),
            'shared':lambda o:o['spends'][1]['shared'].update(nk=o['spends'][1]['shared']['asset']),
            'note-order':lambda o:o['spends'][1]['note'].reverse(),
            'bits':lambda o:o['spends'][1]['amount_bits'].__setitem__(0,o['spends'][0]['amount_bits'][0]),
            'source-product':lambda o:o['nodes'][0].update(multiply=False),
            'source-operand':lambda o:o['nodes'][0].update(left=o['nodes'][0]['right']),
            'selector-lc':lambda o:o['expressions'][next(i for i,x in enumerate(o['expressions']) if x['source']==[2,49])].update(terms=[[967,f'{1:064x}']]),
        }
        for label,mutate in mutations.items():
            obj=copy.deepcopy(base);mutate(obj)
            with self.subTest(label=label),self.assertRaises(relation.RelationError):
                notes.inspect_metadata(encoded(obj),accepted)

    def test_rechecked_persisted_row_semantics_and_full_digest(self):
        args=fixture(); result=notes.extract(*args)
        changed=copy.deepcopy(result);changed['selected_rows'][5]['b'][0][1]=f'{2:064x}'
        with self.assertRaises(relation.RelationError):notes.generate(args[0],changed,args[2])
        raw=args[1].getvalue().replace(f'{1:064x}'.encode(),f'{2:064x}'.encode(),1)
        with self.assertRaisesRegex(relation.RelationError,'do not match relation digest'):
            notes.extract(args[0],io.BytesIO(raw),args[2])

    def test_positive_branches_and_precise_semantic_negative_controls(self):
        args=fixture(); rows=notes.extract(*args)['selected_rows']; p=relation.MODULUS
        def assignment(dummy,amount=None,root=None,nf=None,required_nf=91):
            rho={0:1,1000:1,503:17,961:91,515:required_nf,962:17,513:dummy,966:42,964:19,
                 965:(17 if dummy==0 else 99) if root is None else root,
                 510:(5 if dummy==0 else 0) if amount is None else amount,
                 516:((19+dummy*(42-19))%p) if nf is None else nf}
            operands=[(dummy,42-19),(1-dummy,rho[965]-17),(dummy,rho[510])]
            for i,(left,right) in enumerate(operands):
                rho[967+i]=left*right%p;rho[975+i]=(left-right)**2%p
            return rho
        def rejects(rho):
            def evaluate(terms):return sum(rho.get(c,0)*int(v,16) for c,v in terms)%p
            return [r['row'] for r in rows if evaluate(r['a'])**2%p!=evaluate(r['b'])]
        self.assertEqual(rejects(assignment(0)),[])
        self.assertEqual(rejects(assignment(1)),[])
        self.assertEqual(rejects(assignment(2,root=17)),[3])
        self.assertEqual(rejects(assignment(1,amount=5)),[12])
        self.assertEqual(rejects(assignment(0,root=99)),[9])
        self.assertEqual(rejects(assignment(1,nf=7)),[4])
        self.assertEqual(rejects(assignment(0,required_nf=7)),[1])


if __name__=='__main__':unittest.main()
