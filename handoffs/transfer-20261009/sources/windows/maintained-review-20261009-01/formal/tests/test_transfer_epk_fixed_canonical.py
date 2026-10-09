"""Small comparator/stream fixtures, no qualified native EPK or actual replay credit."""
import copy
import hashlib
import io
import unittest
from circuits import transfer_epk_fixed as epk, transfer_epk_fixed_canonical as module
from circuits import transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine
from tests.test_transfer_epk_all_fixed import all_fixture
from tests.test_transfer_epk_fixed import encoded
from tests.test_transfer_recovery_ranges import fixture as small_relation


def fixture(duplicate=False, missing=False):
    parents = all_fixture(); parent, pages, capsules, caller = parents
    checked = epk.inspect_all_pages(encoded(parent), pages, capsules, caller)
    boundaries = module._boundaries(checked); records = {}; raw = {}; normalized = {}
    def append(a,b):
        index=len(records)
        outline=lambda lc:canonical((200692 if c==0 else c,v) for c,v in lc)
        a,b=outline(a),outline(b); raw[index]=(a,b)
        normalized[index]=tuple(canonical((0 if c==200692 else c,v) for c,v in lc) for lc in (a,b))
        records[index]=dict(row=index,a=[[c,f'{v:064x}'] for c,v in a],b=[[c,f'{v:064x}'] for c,v in b])
    raw[0]=(canonical([(0,1),(200692,-1)]),())
    normalized[0]=((),())
    records[0]=dict(row=0,a=[[c,f'{v:064x}'] for c,v in raw[0][0]],b=[])
    for selected in boundaries:
        scope=selected['scope_id']; before=module.comparator.ONE
        for index,column in enumerate(selected['columns']):
            left=((column,1),); append(left,left)
            right=((module.comparator.ORDER-1)>>index)&1
            both=combine(module.comparator.ONE,left,-1) if right else ()
            factor=combine(combine(module.comparator.ONE,left,-1),((0,right),) if right else ())
            factor=combine(factor,both,-2)
            if index==0:product=factor
            else:
                product=((10000+1000*scope+2*index,1),); auxiliary=((10001+1000*scope+2*index,1),)
                if not (missing and scope==4 and index==7):append(combine(before,factor,-1),auxiliary)
                if duplicate and scope==4 and index==7:append(combine(before,factor,-1),auxiliary)
                append(combine(before,factor),combine(auxiliary,product,4))
            before=combine(both,product)
        append(combine(selected['weighted'],((selected['value'],1),),-1),())
        append(combine(before,module.comparator.ONE,-1),())
    identity=dict(relation_digest=parent['relation_digest'],domain_size=262144,stored_rows=200770)
    return parents,checked,boundaries,identity,raw,normalized,records


class EpkCanonicalTests(unittest.TestCase):
    def test_six_chains_and_scalar_boundary_semantics(self):
        parents,checked,boundaries,identity,raw,normalized,records=fixture()
        derivative=module._derive(checked,boundaries,identity,raw,normalized,records)
        self.assertEqual([len(c['products']) for c in derivative['scopes']],[251]*6)
        for selected,certificate in zip(boundaries,derivative['scopes']):
            pairs={p['step']:p['rows'] for p in certificate['products']}
            endpoint=next(t['row'] for t in certificate['templates'] if t['roles']==['endpoint'])
            for n in (0,1,module.comparator.ORDER-1,module.comparator.ORDER,2**252-1):
                rho={0:1,200692:1,selected['value']:n}
                rho.update((c,(n>>i)&1) for i,c in enumerate(selected['columns']))
                evaluate=lambda lc:sum(rho[c]*v for c,v in lc)%relation.MODULUS
                for i,step in enumerate(certificate['steps']):
                    if i:
                        rho[step['product'][0][0]]=evaluate(step['before'])*evaluate(step['factor'])%relation.MODULUS
                        rho[raw[pairs[i][0]][1][0][0]]=(evaluate(step['before'])-evaluate(step['factor']))**2%relation.MODULUS
                failing=[r['row'] for r in certificate['selected_rows']
                    if evaluate(raw[r['row']][0])**2%relation.MODULUS!=evaluate(raw[r['row']][1])]
                self.assertEqual(failing,[] if n<module.comparator.ORDER else [endpoint])
        parent,pages,capsules,caller=parents
        source=module.generate(encoded(parent),pages,capsules,caller,derivative,5)
        self.assertIn('RuntimeTransferEpk5Canonical',source)
        self.assertEqual(source.count('#print axioms'),7)
        self.assertEqual(source.count('#check @'),7)
        plan=module.construction_plan(encoded(parent),pages,capsules,caller,derivative)
        self.assertEqual([len(s['stages']) for s in plan['scopes']],[251]*6)
        self.assertTrue(plan['capacity'])
        self.assertFalse(set(plan['writes']) & set(plan['protected']))
        self.assertEqual(len(plan['writes']),6*(252+2*251))
        self.assertIn('No desired point/inverse/endpoint premise',plan['native_seed_contract'])
        changed=copy.deepcopy(derivative);changed['scopes'][5]['steps'][7]['right']=True
        with self.assertRaisesRegex(relation.RelationError,'certificate changed'):
            module.generate(encoded(parent),pages,capsules,caller,changed,5)

    def test_physical_ambiguity_missing_pair_and_identity_refused(self):
        for options in (dict(duplicate=True),dict(missing=True)):
            _,checked,boundaries,identity,raw,normalized,records=fixture(**options)
            with self.assertRaisesRegex(relation.RelationError,'unique product pair'):
                module._derive(checked,boundaries,identity,raw,normalized,records)
        _,checked,boundaries,identity,raw,normalized,records=fixture()
        identity['relation_digest']='f'*64
        with self.assertRaisesRegex(relation.RelationError,'identity/shape'):
            module._derive(checked,boundaries,identity,raw,normalized,records)

    def test_tap_preserves_complete_bytes_and_refuses_truncation_tail_and_reuse(self):
        # This small stream is a real complete serialized relation fixture;
        # its identity is not the production200770 relation or EPK qualifier.
        _,_,_,data=small_relation()
        plain=relation.inspect(io.BytesIO(data))
        tap=module._CandidateStream(io.BytesIO(data),[dict(columns=list(range(10,262)))],4000)
        observed=relation.inspect(tap)
        self.assertEqual(observed,plain)
        self.assertEqual(observed['raw_sha256'],hashlib.sha256(data).hexdigest())
        self.assertTrue(tap.eof and tap.tail_checked)
        with self.assertRaisesRegex(relation.RelationError,'after EOF'):tap.readline()
        with self.assertRaisesRegex(relation.RelationError,'lifecycle'):tap.read(1)
        for changed in (data[:-1],data+b'x'):
            with self.assertRaises(relation.RelationError):
                relation.inspect(module._CandidateStream(io.BytesIO(changed),[dict(columns=[])],4000))

    def test_candidate_bounds_stop_before_retaining_extra(self):
        from unittest.mock import patch
        line=encoded(dict(row=0,a=[[10,f'{1:064x}']],b=[]))
        tap=module._CandidateStream(io.BytesIO(line),[dict(columns=[10])],200692)
        with patch.object(module,'MAX_ROWS',0),self.assertRaisesRegex(relation.RelationError,'bounded candidate'):
            tap.readline()
        self.assertEqual(tap.records,{})


if __name__=='__main__':unittest.main()
