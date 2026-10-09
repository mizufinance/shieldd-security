"""Bounded original boundary fixtures; no lawful EPK/capture/whole-cone credit."""
import copy
import unittest
from circuits import transfer_epk_fixed as epk,transfer_epk_fixed_rows as module,transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_epk_all_fixed import all_fixture
from tests.test_transfer_epk_fixed import encoded


def fixture(negative=True):
    parents=all_fixture();parent,pages,capsules,caller=parents
    checked=epk.inspect_all_pages(encoded(parent),pages,capsules,caller)
    copy_column=200692;records=[];templates=[];products=[]
    def append(a,b):
        outline=lambda lc:canonical((copy_column if c==0 else c,v) for c,v in lc)
        index=len(records);records.append(dict(row=index,
            a=[[c,f'{v:064x}'] for c,v in outline(a)],b=[[c,f'{v:064x}'] for c,v in outline(b)]))
        return index
    records.append(dict(row=0,a=[[0,f'{1:064x}'],[copy_column,f'{relation.MODULUS-1:064x}']],b=[]))
    templates.append(dict(row=0,roles=['boundary.constant-copy']))
    for scope in module._roles(checked):
        ordinal=scope['scope_id'];prefix=f'boundary.scope.{ordinal}.'
        for axis,(published,computed) in enumerate(zip(scope['published'],scope['computed'])):
            equation=combine(published,computed,-1)
            index=append(canonical((c,-v) for c,v in equation) if negative else equation,())
            templates.append(dict(row=index,roles=[prefix+f'bind.{axis}']))
        q=scope['inverse'];x=scope['published'][0]
        output=((190000+2*ordinal,1),);auxiliary=((190001+2*ordinal,1),)
        indices=[append(combine(q,x,-1),auxiliary),append(combine(q,x),combine(auxiliary,output,4))]
        equation=combine(output,((0,1),),-1)
        indices.append(append(canonical((c,-v) for c,v in equation) if negative else equation,()))
        products.append(dict(role=prefix+'inverse',rows=indices))
    identity=dict(relation_digest=parent['relation_digest'],stored_rows=200770,domain_size=262144)
    combined=dict(identity=identity,selected_rows=records,templates=templates,products=products)
    return parents,checked,combined


class EpkBoundaryTests(unittest.TestCase):
    def test_both_original_signs_and_six_inverse_footprints(self):
        for negative in (False,True):
            parents,checked,combined=fixture(negative);extracted=module.boundary_selection(checked,combined)
            parent,pages,capsules,caller=parents
            plan=module.boundary_plan(encoded(parent),pages,capsules,caller,extracted)
            self.assertEqual(len(plan['writes']),18)
            self.assertFalse(set(plan['writes'])&set(plan['protected']))
            for scope in plan['scopes']:
                self.assertEqual(scope['inverse_assertion_negative'],negative)
                self.assertTrue(all(binding['negative']==negative for binding in scope['bindings']))
            # Only the inverse triples are tested under legal/nonlegal x here.
            # The folded native-identity source fixture cannot satisfy its
            # published binding and inverse simultaneously: no full EPK proof.
            raw={r['row']:r for r in extracted['selected_rows']}
            for x in (0,1,7):
                rho={0:1,200692:1}
                for scope in plan['scopes']:
                    stage=scope['inverse_constructor'];q=pow(x,-1,relation.MODULUS) if x else 0
                    rho[scope['published'][0][0][0]]=x
                    rho[stage['quotient']]=q;rho[stage['product']]=1;rho[stage['auxiliary']]=(q-x)**2%relation.MODULUS
                    failed=[]
                    for index in stage['rows']:
                        row=raw[index]
                        a,b=(sum(rho[c]*int(v,16) for c,v in row[side])%relation.MODULUS for side in ('a','b'))
                        if a*a%relation.MODULUS!=b:failed.append(index)
                    self.assertEqual(failed,[stage['rows'][1]] if x==0 else [])

    def test_changed_assertion_coverage_parent_and_protected_pivot_refused(self):
        parents,checked,combined=fixture();original=module.boundary_selection(checked,combined)
        parent,pages,capsules,caller=parents
        for edit in ('sign','missing','extra','parent','pivot'):
            changed=copy.deepcopy(original)
            if edit=='sign':changed['selected_rows'][1]['a'][0][1]=f'{2:064x}'
            elif edit=='missing':changed['selected_rows'].pop()
            elif edit=='extra':changed['selected_rows'].append(dict(row=199000,a=[[12345,f'{1:064x}']],b=[]))
            elif edit=='parent':changed['parent_sha256']='f'*64
            else:
                # Reuse a real shared scalar column as the product pivot in
                # both plus/assertion rows. Arithmetic remains an exact
                # quotient, but constructive ownership must reject it.
                for row in changed['selected_rows']:
                    for side in ('a','b'):
                        row[side]=sorted([[3 if c==190000 else c,v] for c,v in row[side]])
            with self.subTest(edit=edit),self.assertRaises(relation.RelationError):
                module.boundary_plan(encoded(parent),pages,capsules,caller,changed)


if __name__=='__main__':unittest.main()
