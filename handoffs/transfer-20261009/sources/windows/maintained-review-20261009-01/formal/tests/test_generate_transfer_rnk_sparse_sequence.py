"""Synthetic finite renderer fixtures; no runtime observation/proof qualification."""
import copy
import re
import unittest

from circuits import transfer_rnk_completion as completion
from circuits import generate_transfer_rnk_sparse_sequence as generator
from circuits.transfer_relation import RelationError
from tests.test_transfer_rnk_completion import row


class SyntheticRnkSequenceRendererTests(unittest.TestCase):
    def fixture(self):
        blocks=[];roles=[];physical=0
        def append(source,writes,role):
            nonlocal physical
            original=[];actual=[]
            for a,b in source:
                original.append(row(physical,a,b))
                rename=lambda lc:[(completion.ownership.rnk_column_candidate(c),v) for c,v in lc]
                actual.append(row(10000+physical,rename(a),rename(b)))
                physical+=1
            blocks.append(dict(source_rows=original,target_rows=actual,source_writes=sorted(writes)))
            roles.append(role)
        for start in range(0,126,16):
            count=min(16,126-start)
            for index in range(start,start+count):
                column=2253+index;writes=[column]
                source=[([(column,1)],[(2000+index,1)])]
                if index==0:
                    source.extend([([(1504,1),(1505,1)],[]), ([(0,1),(200692,-1)],[])])
                if index==125:
                    source.extend([([(3007,1)],[]), ([(3008,1)],[])])
                    writes.extend([3007,3008])
                append(source,writes,dict(kind='window',window=index,chunk=start))
            low=2*(126-start-count)
            append([([(2000+i,1)],[(2000+i,1)]) for i in range(low,low+2*count)],[],
                dict(kind='bits',chunk=start,bit_start=low,width=2*count))
        plan=completion.sparse_sequence_plan(blocks,domain_size=262144,full_rows=200770,
            protected_columns=[0,1512,1513,1520,1521,1980,1981,1993,3007,3008,3766,200692])
        plan.update(schema='shieldd-transfer-rnk-all126-sparse-plan-v1',windows=126,
            row_blocks=blocks,roles=roles,bit_start=2000,bit_width=252,
            identity={'scope':'synthetic finite fixture; not captured or qualified'})
        return plan

    def inventory(self,source):
        checks=re.findall(r'^#check @([^\s]+)',source,re.M)
        prints=re.findall(r'^#print axioms ([^\s]+)',source,re.M)
        self.assertEqual(checks,prints);self.assertEqual(len(checks),len(set(checks)))
        return len(checks)

    def test_finite_block_names_rows_and_exact_audit_inventory(self):
        modules=generator.generate_blocks(self.fixture())
        self.assertEqual(len(modules),134)
        self.assertEqual(sum(self.inventory(source) for source in modules.values()),536)
        self.assertIn('RuntimeOwnershipWindow125.rawRows',modules['RuntimeRnkSparseBlock132'])
        self.assertIn("List.range' 0 28",modules['RuntimeRnkSparseBlock133'])

    def test_one_assignment_and_eight_native_chunks_without_desired_row_premise(self):
        plan=self.fixture()
        _,source=generator.generate_assignment(plan,constant_copy=200692)
        self.assertEqual(self.inventory(source),8)
        self.assertIn('GroupSparseRenamingSequence.run',source)
        self.assertIn('RuntimeRnkNativeSource.sourceAssignment',source)
        chunks=generator.generate_native_chunks(plan,constant_copy=200692)
        self.assertEqual(len(chunks),8)
        self.assertEqual(sum(self.inventory(value) for value in chunks.values()),8)
        for value in chunks.values():
            self.assertIn('RuntimeRnkNativeSource.source_original_complete',value)
            self.assertIn('RuntimeRnkNativeSource.source_boolean_complete',value)
            self.assertNotRegex(value,r'\((?:satisfied|constructed)\s*:')
        _,joined=generator.generate_join(plan,constant_copy=200692)
        self.assertEqual(self.inventory(joined),2)
        self.assertIn('fr.integer scalar',joined)
        self.assertNotRegex(joined,r'\((?:satisfied|constructed)\s*:')

    def test_role_and_whole_certificate_tampering_refused(self):
        for key in ('roles','source_writes','nonwritten_support','column_pairs'):
            plan=self.fixture();plan[key].pop()
            with self.assertRaises(RelationError):generator.generate_blocks(plan)
        plan=self.fixture();plan['row_blocks'][0]['target_rows'][0]['b'][0][1]=format(2,'064x')
        with self.assertRaises(RelationError):generator.generate_blocks(plan)

    def test_missing_owned_output_and_invented_copy_refused(self):
        plan=self.fixture()
        for value in (True,0,200693):
            with self.assertRaises(RelationError):generator.generate_assignment(plan,constant_copy=value)
        changed=copy.deepcopy(plan)
        # A structurally valid narrow plan cannot claim the actual final output
        # if its source ownership does not include the final source columns.
        changed['row_blocks'][132]['source_writes']=[2378]
        updated=completion.sparse_sequence_plan(changed['row_blocks'],domain_size=262144,
            full_rows=200770,protected_columns=plan['protected_columns'])
        changed.update({key:value for key,value in updated.items() if key not in ('schema','scope')})
        with self.assertRaisesRegex(RelationError,'final output'):
            generator.generate_assignment(changed,constant_copy=200692)


if __name__=='__main__':unittest.main()
