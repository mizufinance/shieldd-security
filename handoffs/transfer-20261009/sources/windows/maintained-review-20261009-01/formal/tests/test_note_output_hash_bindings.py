"""Actual supplied assertion construction, freshness refusal and row control."""
import io,json,unittest
from circuits import transfer_note_output_hash as hashes,transfer_note_output_bindings as bindings,transfer_relation as relation
from tests.test_note_output_hash import fixture
from tests.test_transfer_note_spend import encoded
from tests.test_transfer_note_outputs import fixture as core_fixture
from circuits import transfer_note_outputs as outputs


class OutputHashBindingTests(unittest.TestCase):
    def test_note_and_recovery_actual_assertions_construct_only_the_supplied_witness(self):
        for role in ('note','recovery'):
            pages,outputs,caller,artifact,rows=fixture(role)
            extracted=hashes.extract_binding(pages[1],io.BytesIO(rows),outputs,caller)
            selected=bindings.plan(pages[1],extracted,outputs,caller);p=relation.MODULUS
            rho={c:(41*c+17)%p for c in range(4096)};rho[0]=rho[4000]=1;original=dict(rho)
            rho[selected['target']]=sum(rho[c]*v for c,v in selected['computed'])%p
            evaluate=lambda terms:sum(rho[c]*v for c,v in terms)%p
            a,b=selected['raw_row'];self.assertEqual(evaluate(a)**2%p,evaluate(b))
            self.assertTrue(all(rho[c]==original[c] for c in original if c!=selected['target']))
            name,source=bindings.generate(pages[1],extracted,outputs,caller)
            self.assertEqual(source.count('#print axioms'),6)
            signature=source[source.index('theorem complete_rows'):source.index(' := by',source.index('theorem complete_rows'))]
            self.assertNotIn('(satisfied :',signature);self.assertNotIn('computed =',signature)
            rho[selected['target']]=(rho[selected['target']]+1)%p
            self.assertNotEqual(evaluate(a)**2%p,evaluate(b))

    def test_shared_supplied_owner_alias_is_refused(self):
        pages,outputs,caller,artifact,rows=fixture('recovery')
        extracted=hashes.extract_binding(pages[1],io.BytesIO(rows),outputs,caller)
        changed={**caller,'observed':dict(caller['observed'])};obj=json.loads(pages[1])
        ref=tuple(obj['supplied_commitment']['source']);column=ref[1]+3
        changed['observed'][ref]=((column,1),)
        with self.assertRaisesRegex(relation.RelationError,'aliases shared'):
            bindings.plan(pages[1],extracted,outputs,changed)

    def test_both_capsule_commitments_construct_the_actual_note_recovery_inputs(self):
        data,caller,stream,rows=core_fixture();extracted=outputs.extract(data,stream,caller)
        p=relation.MODULUS
        for slot in (0,1):
            selected=bindings.capsule_copy_plan(data,extracted,caller,slot)
            rho={c:(29*c+13)%p for c in range(4096)};rho[0]=rho[4000]=1;original=dict(rho)
            rho[selected['target']]=sum(rho[c]*v for c,v in selected['computed'])%p
            evaluate=lambda terms:sum(rho[c]*v for c,v in terms)%p
            a,b=selected['raw_row'];self.assertEqual(evaluate(a)**2%p,evaluate(b))
            self.assertTrue(all(rho[c]==original[c] for c in original if c!=selected['target']))
            _,source=bindings.generate_capsule_copy(data,extracted,caller,slot)
            self.assertEqual(source.count('#print axioms'),6)
            rho[selected['target']]=(rho[selected['target']]+1)%p
            self.assertNotEqual(evaluate(a)**2%p,evaluate(b))


if __name__=='__main__':unittest.main()
