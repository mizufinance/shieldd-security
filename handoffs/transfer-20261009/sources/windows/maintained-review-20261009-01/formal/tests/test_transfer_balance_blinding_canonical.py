"""Actual-shaped scalar row fixtures, including0/order boundary; no capture credit."""
import copy,unittest
from circuits import transfer_balance_blinding_fixed as ingress,transfer_balance_blinding_canonical as scalar
from circuits import transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_balance_blinding import fixture as pages_fixture,encoded


def fixture(missing=False,duplicate=False):
    parent,pages,base,blinding=pages_fixture();checked=ingress.inspect_pages(encoded(parent),pages,base,blinding)
    selected=scalar.boundary(checked);raw={};normalized={};records={}
    def append(a,b):
        index=len(records);outline=lambda lc:canonical((200692 if c==0 else c,v) for c,v in lc)
        a,b=outline(a),outline(b);raw[index]=(a,b)
        normalized[index]=tuple(canonical((0 if c==200692 else c,v) for c,v in side) for side in (a,b))
        records[index]=dict(row=index,a=[[c,f'{v:064x}'] for c,v in a],b=[[c,f'{v:064x}'] for c,v in b])
    append(canonical([(0,1),(200692,-1)]),())
    raw[0]=(canonical([(0,1),(200692,-1)]),())
    normalized[0]=((),());records[0]=dict(row=0,a=[[c,f'{v:064x}'] for c,v in raw[0][0]],b=[])
    before=scalar.comparator.ONE
    for i,column in enumerate(selected['columns']):
        left=((column,1),);append(left,left);right=(scalar.comparator.ORDER-1)>>i&1
        both=combine(scalar.comparator.ONE,left,-1) if right else ()
        factor=combine(combine(scalar.comparator.ONE,left,-1),((0,right),) if right else ())
        factor=combine(factor,both,-2)
        if not i:product=factor
        else:
            product=((10000+2*i,1),);auxiliary=((10001+2*i,1),)
            if not(missing and i==7):append(combine(before,factor,-1),auxiliary)
            if duplicate and i==7:append(combine(before,factor,-1),auxiliary)
            append(combine(before,factor),combine(auxiliary,product,4))
        before=combine(both,product)
    append(combine(selected['weighted'],((selected['value'],1),),-1),())
    append(combine(before,scalar.comparator.ONE,-1),())
    identity=dict(relation_digest=ingress.DIGEST,domain_size=262144,stored_rows=200770)
    return (parent,pages,base,blinding),checked,selected,identity,raw,normalized,records


class BlindingCanonicalTests(unittest.TestCase):
    def test_asset_column_is_kept_and_real_chain_pivot_alias_refuses_without_readonly(self):
        _,checked,_,identity,raw,normalized,records=fixture()
        derivative=scalar._derive(checked,identity,raw,normalized,records)
        self.assertIn(6,scalar.construction_plan(checked,derivative)['kept'])
        # Preserve every local polynomial while moving a genuine product pivot
        # into the earlier asset witness. Exact arithmetic is insufficient when
        # the assignment would destroy a shared input.
        for index,row in list(raw.items()):
            raw[index]=tuple(canonical((6 if c==10012 else c,v) for c,v in side) for side in row)
            normalized[index]=tuple(canonical((0 if c==200692 else c,v) for c,v in side) for side in raw[index])
            records[index]=dict(row=index,a=[[c,f'{v:064x}'] for c,v in raw[index][0]],
                                b=[[c,f'{v:064x}'] for c,v in raw[index][1]])
        changed=scalar._derive(checked,identity,raw,normalized,records)
        with self.assertRaisesRegex(relation.RelationError,'freshness/ownership'):
            scalar.construction_plan(checked,changed)

    def test_zero_is_constructed_but_order_endpoint_is_rejected(self):
        _,checked,selected,identity,raw,normalized,records=fixture()
        derivative=scalar._derive(checked,identity,raw,normalized,records)
        certificate=derivative['certificate'];plan=scalar.construction_plan(checked,derivative,readonly_lcs=(((6,1),),))
        self.assertEqual(len(plan['stages']),251);self.assertEqual(len(plan['writes']),754)
        self.assertTrue({0,1,2,3,6,200692}<=set(plan['kept']))
        self.assertIn('Zero is legal',plan['native_seed_contract'])
        endpoint=next(t['row'] for t in certificate['templates'] if t['roles']==['endpoint'])
        pairs={p['step']:p['rows'] for p in certificate['products']}
        for n in (0,1,scalar.comparator.ORDER-1,scalar.comparator.ORDER,2**252-1):
            rho={0:1,200692:1,selected['value']:n};rho.update((c,(n>>i)&1) for i,c in enumerate(selected['columns']))
            evaluate=lambda lc:sum(rho[c]*v for c,v in lc)%relation.MODULUS
            for i,step in enumerate(certificate['steps']):
                if i:
                    rho[step['product'][0][0]]=evaluate(step['before'])*evaluate(step['factor'])%relation.MODULUS
                    rho[raw[pairs[i][0]][1][0][0]]=(evaluate(step['before'])-evaluate(step['factor']))**2%relation.MODULUS
            failures=[r['row'] for r in certificate['selected_rows'] if evaluate(raw[r['row']][0])**2%relation.MODULUS!=evaluate(raw[r['row']][1])]
            self.assertEqual(failures,[] if n<scalar.comparator.ORDER else [endpoint])

    def test_missing_duplicate_and_changed_physical_certificates_refuse(self):
        for options in (dict(missing=True),dict(duplicate=True)):
            _,checked,_,identity,raw,normalized,records=fixture(**options)
            with self.assertRaisesRegex(relation.RelationError,'unique product pair'):scalar._derive(checked,identity,raw,normalized,records)
        _,checked,_,identity,raw,normalized,records=fixture();derivative=scalar._derive(checked,identity,raw,normalized,records)
        for change in ('recurrence','row','flag','parent','bool','readonly'):
            altered=copy.deepcopy(derivative)
            if change=='recurrence':altered['certificate']['steps'][4]['right']^=1
            elif change=='row':altered['certificate']['selected_rows'].pop()
            elif change=='flag':altered['ordinary_replays']=True
            elif change=='parent':altered['parent_sha256']='f'*64
            elif change=='bool':altered['certificate']['steps'][4]['right']=bool(altered['certificate']['steps'][4]['right'])
            with self.subTest(change=change),self.assertRaises(relation.RelationError):
                scalar.construction_plan(checked,altered,readonly_lcs=(((13,1),),) if change=='readonly' else ())

    def test_neutral_rendering_has_no_positive_or_inverse_premise(self):
        parents,checked,_,identity,raw,normalized,records=fixture();derivative=scalar._derive(checked,identity,raw,normalized,records)
        sources=scalar.generate(encoded(parents[0]),*parents[1:],derivative)
        self.assertEqual(len(sources),3)
        for source in sources.values():
            self.assertEqual(source.count('#print axioms'),source.count('set_option pp.all true in'))
            self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        complete=sources['RuntimeBalanceBlindingCanonicalCompletion']
        self.assertIn('(canonical : n < Scalar.order)',complete)
        self.assertNotIn('(positive :',complete);self.assertNotIn('(inverse :',complete)
        self.assertIn('actual_original_rows_complete',complete);self.assertIn('bit_reflection',complete)
