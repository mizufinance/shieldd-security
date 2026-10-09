"""Diagnostic RK construction generation from typed rows, not runtime evidence."""
import copy
import io
import json
import re
import unittest
from circuits import generate_transfer_rk_subgroup as generator, transfer_rk_subgroup as rk
from tests.test_transfer_rk_subgroup import fixture


class RkSubgroupGenerationTests(unittest.TestCase):
    def setUp(self):
        obj,self.roles,stream=fixture();self.data=(json.dumps(obj)+'\n').encode()
        self.extracted=rk.extract(self.data,self.roles,io.BytesIO(stream))

    def test_materialization_covers_every_nonlinear_row_and_preserves_witnesses(self):
        plan=generator.completion_plan(self.data,self.roles,self.extracted)
        self.assertTrue(plan['stages'])
        self.assertEqual(set(plan['materialization_rows'])|{plan['roles'][r] for r in plan['assertions']},set(plan['raw']))
        self.assertTrue(set(self.extracted['allocation']['witnesses'])<=set(plan['kept']))
        source=generator.generate_materialization(self.data,self.roles,self.extracted)
        self.assertIn('GroupCircuitOrder.checked_order',source)
        self.assertIn('GroupCircuitCompletion.original_rows_complete',source)
        theorem=source.split('theorem materialized_complete',1)[1].split('theorem eval_kept',1)[0]
        self.assertNotIn('(satisfied',theorem)
        audits=re.findall(r'#check @([\w]+)',source)
        self.assertEqual(len(audits),5);self.assertEqual(len(audits),len(set(audits)))
        self.assertNotRegex(source,r'\b(?:sorry|admit|axiom)\b')

    def test_cones_use_constructed_rows_without_native_assertions(self):
        selected=generator.cone_selection(self.data,self.roles,self.extracted)
        self.assertEqual(len(selected['cones']),11)
        plan=generator.completion_plan(self.data,self.roles,self.extracted)
        self.assertEqual(set(selected['rows']),set(plan['materialization_rows']))
        self.assertFalse(set(selected['rows']) & {plan['roles'][r] for r in plan['assertions']})
        source=generator.generate_cones(self.data,self.roles,self.extracted)
        self.assertIn('namespace ShielddSecurity.RuntimeTransferRkSubgroupCones',source)
        self.assertIn('theorem double2_after_y_sound',source)
        audits=re.findall(r'#check @([\w]+)',source)
        self.assertTrue(audits);self.assertEqual(len(audits),len(set(audits)))

    def test_json_roundtrip_regenerates_identical_candidates(self):
        loaded=json.loads(json.dumps(self.extracted))
        self.assertEqual(generator.generate_materialization(self.data,self.roles,loaded),generator.generate_materialization(self.data,self.roles,self.extracted))
        self.assertEqual(generator.generate_cones(self.data,self.roles,loaded),generator.generate_cones(self.data,self.roles,self.extracted))
        self.assertEqual(generator.generate_native_completion(self.data,self.roles,loaded),generator.generate_native_completion(self.data,self.roles,self.extracted))

    def test_native_transport_constructs_witnesses_and_derives_assertions(self):
        source=generator.generate_native_completion(self.data,self.roles,self.extracted)
        self.assertIn('GroupNativeSubgroupWitness.native_subgroup_constraints',source)
        self.assertIn('patchAssignment base (witnessValues',source)
        self.assertIn('have materialized : Satisfies built',source)
        statement=source.split('theorem actual_rows_complete',1)[1].split(':= by',1)[0]
        self.assertNotIn('(satisfied',statement)
        self.assertNotIn('eight =',statement)
        self.assertNotIn('inverseEquation',statement)
        self.assertIn('(subgroup : Scalar.order • point = 0)',statement)
        self.assertIn('(nonidentity : point ≠ 0)',statement)
        self.assertNotIn('namespace M :=',source)
        audits=re.findall(r'#check @([\w]+)',source)
        self.assertEqual(len(audits),4);self.assertEqual(len(audits),len(set(audits)))
        self.assertNotRegex(source,r'\b(?:sorry|admit|axiom)\b')

    def test_changed_allocation_and_assertions_refuse(self):
        cases=[lambda x:x['allocation']['witnesses'].pop(),
               lambda x:x['allocation']['stages'][0]['writes'].__setitem__(0,13),
               lambda x:x['allocation']['stages'][0]['source'].__setitem__(1,9999),
               lambda x:x['allocation']['nonlinear_writes'].pop(),
               lambda x:x['selected_rows'][-1]['a'][0].__setitem__(1,f'{2:064x}')]
        for mutate in cases:
            changed=copy.deepcopy(self.extracted);mutate(changed)
            with self.subTest(mutate=mutate),self.assertRaises(rk.relation.RelationError):
                generator.completion_plan(self.data,self.roles,changed)

    def test_malformed_retained_allocations_are_typed_refusals(self):
        for mutate in (lambda x:x['allocation'].__setitem__('witnesses',None),
                       lambda x:x['allocation']['stages'][0].__setitem__('writes',None),
                       lambda x:x.__setitem__('templates',None),
                       lambda x:x['templates'][0].__setitem__('row',True)):
            changed=copy.deepcopy(self.extracted);mutate(changed)
            with self.subTest(mutate=mutate),self.assertRaises(rk.relation.RelationError):
                generator.completion_plan(self.data,self.roles,changed)

    def test_reversed_actual_difference_square_keeps_source_and_checks_commutation(self):
        def reverse(rows):
            # First product in the independent curve/right cone.
            index=next(i for i in range(len(rows)-1) if len(rows[i]['b'])==1 and len(rows[i+1]['b'])==2
                       and rows[i]['b'][0] in rows[i+1]['b'])
            for term in rows[index]['a']:term[1]=f'{(-int(term[1],16))%rk.P:064x}'
        obj,roles,stream=fixture(reverse);data=(json.dumps(obj)+'\n').encode()
        extracted=rk.extract(data,roles,io.BytesIO(stream))
        source=generator.generate_cones(data,roles,extracted)
        self.assertIn('simpa only [mul_comm] using (Compiler.checked_product_sound',source)
        self.assertIn('theorem curve_right_sound',source)
        generator.generate_materialization(data,roles,extracted)
        generator.generate_native_completion(data,roles,extracted)

    def test_independent_legal_point_constructs_all_original_fixture_rows(self):
        # Numerical field check of the constructor recipe on an independently
        # admitted subgroup point. This is a typed fixture control, not a Lean
        # proof or an observation of a runtime witness-generation closure.
        p=rk.P;d=rk.D;order=6554484396890773809930967563523245729705921265872317281365359162392183254199
        inverse_eight=(6490498278660957591+1498858728380236304*2**64+
                       2363518304504940384*2**128+130523700929132021*2**192)
        self.assertEqual(8*inverse_eight,order+1)
        def add(a,b):
            x,y=a;u,v=b;delta=d*x*u*y*v%p
            self.assertNotEqual((1+delta)%p,0);self.assertNotEqual((1-delta)%p,0)
            return ((x*v+y*u)*pow((1+delta)%p,-1,p)%p,(y*v+x*u)*pow((1-delta)%p,-1,p)%p)
        def multiply(point,n):
            result=(0,1)
            while n:
                if n&1:result=add(result,point)
                point=add(point,point);n>>=1
            return result
        seed_point=(3,26155723652191673091881779851507865815856437797311909079256717375290769542325)
        public=multiply(seed_point,8)
        self.assertNotEqual(public,(0,1));self.assertEqual(multiply(public,order),(0,1))
        self.assertEqual((public[1]**2-public[0]**2-1-d*public[0]**2*public[1]**2)%p,0)
        preimage=multiply(public,inverse_eight);before=preimage
        plan=generator.completion_plan(self.data,self.roles,self.extracted);state=plan['state'];rho={0:1,state['metadata']['constant_copy']:1}
        for h,value in zip(state['inputs'][:4],public+preimage):rho[3+h[1]]=value
        caller_before={c:rho[c] for c in (0,state['metadata']['constant_copy'],13,14)}
        for h in state['formulas']['inverse_witnesses']:
            delta=d*before[0]**2*before[1]**2%p
            rho[3+h[1]]=pow((1-delta*delta)%p,-1,p);before=add(before,before)
        self.assertEqual(before,public)
        rho[3+state['nonidentity'][1][1]]=pow(public[0],-1,p)
        def evaluate(terms):return sum(v*rho.get(c,0) for c,v in terms)%p
        for stage in plan['stages']:
            if stage['kind']=='square':rho[stage['output']]=(evaluate(stage['input'])**2-evaluate(stage['remainder']))%p
            else:
                left,right,remainder=(evaluate(stage[k]) for k in ('left','right','remainder'))
                rho[stage['output']]=(left*right-remainder)%p
                rho[stage['auxiliary']]=(left-right)**2%p
        rejected=[i for i,(a,b) in plan['raw'].items() if evaluate(a)**2%p != evaluate(b)]
        self.assertEqual(rejected,[])
        self.assertEqual({c:rho[c] for c in caller_before},caller_before)
        # The final y binding is necessary on this SAME constructed assignment.
        original=plan['raw'][plan['roles']['rk-link.1']]
        changed=tuple((c,(-v)%p if c==14 else v) for c,v in original[0])
        self.assertNotEqual(evaluate(changed)**2%p,evaluate(original[1]))


if __name__=='__main__':unittest.main()
