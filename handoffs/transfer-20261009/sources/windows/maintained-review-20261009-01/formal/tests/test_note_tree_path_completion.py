"""Construct24 actual field-state levels, checking all prior emitted rows."""
import copy,tempfile,unittest
from pathlib import Path
from circuits import generate_note_tree_path_completion as completion,generate_note_tree_path as sound
from circuits import transfer_note_tree as tree,transfer_relation as relation
from tests.note_tree_path_fixture import path_fixture
from tests.test_note_hash_block_completion import native_rounds


class NoteTreePathCompletionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory=tempfile.TemporaryDirectory();cls.root=Path(cls.directory.name);cls.fixture=path_fixture(cls.root)
    @classmethod
    def tearDownClass(cls):cls.directory.cleanup()
    def plan(self,index,prior=(),**overrides):
        f=self.fixture
        return completion.level_plan(f['data'],overrides.get('tree',f['tree'][index]),
            overrides.get('page',f['pages'][index]),overrides.get('hash',f['hashes'][index]),
            f['note'],f['caller'],self.root,0,index,prior)

    def test_construct_full24_native_path_preserving_all_earlier_actual_rows(self):
        f=self.fixture;p=relation.MODULUS;rho={c:(13*c+17)%p for c in range(32768)};rho[0]=rho[32000]=1
        checked=tree.inspect_metadata(f['data'],f['note'],f['caller'])
        evaluate=lambda terms:sum(rho[c]*v for c,v in terms)%p
        for i,current in enumerate(checked['levels'][:24]):
            rho[current['low'][0][0]]=i%2;rho[current['high'][0][0]]=(i//2)%2
        initial=dict(rho);prior=[];owned=set();stages=[];floors=[]
        for i in range(24):
            plan=self.plan(i,prior);current=plan['routing']['current']
            position=i%4;children=[evaluate(lc) for lc in current['siblings']];children.insert(position,evaluate(current['node']))
            for step in plan['routing']['steps']:
                left,right=evaluate(step['left']),evaluate(step['right'])
                rho[step['auxiliary']]=(left-right)**2%p
                rho[step['output']]=(left*right-evaluate(step['remainder']))%p
            self.assertEqual([evaluate(lc) for lc in current['children']],children)
            native=native_rounds([1281,i+1,*children],f['artifact'],0,65)
            for chunk in plan['chunks']:
                for step in chunk['steps']:
                    left=evaluate(step['left'])
                    if step['kind']=='square':value=left*left
                    else:
                        right=evaluate(step['right']);value=left*right;rho[step['auxiliary']]=(left-right)**2%p
                    rho[step['output']]=(value-evaluate(step['remainder']))%p
            self.assertEqual(evaluate(current['output']),native[1])
            prior.extend(plan['raw']);owned.update(plan['writes']);floors.append(plan['floor'])
            self.assertTrue(all(evaluate(a)**2%p==evaluate(b) for a,b in prior))
            self.assertTrue(all(rho[c]==initial[c] for c in initial if c not in owned))
            name,source=completion._level_source(plan,stages);stages.append(name)
            self.assertEqual(source.count('#print axioms'),9)
            self.assertIn('ColumnFence.checked_rows',source)
            self.assertIn('complete_level',source)
        name,source=completion._composition(checked,0,stages,floors)
        self.assertEqual(name,'RuntimeTransferNoteTree0PathCompletion')
        self.assertEqual(source.count('#print axioms'),7)
        statement=source[source.index('theorem complete_path'):source.index(' := by',source.index('theorem complete_path'))]
        self.assertNotIn('(satisfied :',statement);self.assertNotIn('(rootValue :',statement)
        self.assertIn('TreeBinding.root',statement);self.assertIn('lowValue',statement)
        self.assertNotIn('sorry',source);self.assertNotIn('native_decide',source)
        self.assertNotIn('sound_coverage_checked :',source) # no quadratic all-path membership check
        self.assertEqual(sound._join_source(checked,0)[1].count('#print axioms'),26)
        rho[next(iter(owned))]=(rho[next(iter(owned))]+1)%p
        self.assertFalse(all(evaluate(a)**2%p==evaluate(b) for a,b in prior))

    def test_closed_source_rows_prior_fences_and_exact_page_order_refused(self):
        f=self.fixture
        with self.assertRaisesRegex(relation.RelationError,'exact source order|exact state page order'):
            self.plan(0,page=f['pages'][1])
        changed=copy.deepcopy(f['hashes'][0]);changed['selected_rows'].pop()
        with self.assertRaisesRegex(relation.RelationError,'missing'):self.plan(0,hash=changed)
        changed=copy.deepcopy(f['tree'][0]);changed['selected_rows'].pop()
        with self.assertRaises(relation.RelationError):self.plan(0,tree=changed)
        with self.assertRaisesRegex(relation.RelationError,'prior actual row fence'):
            self.plan(0,prior=[(((5000,1),),())])
        for inventories in (([],f['pages'],f['hashes']),(f['tree'][:24],f['pages'][:-1],f['hashes'])):
            with self.assertRaisesRegex(relation.RelationError,'exact24'):
                next(completion.generate(f['data'],*inventories,f['note'],f['caller'],self.root,0))


if __name__=='__main__':unittest.main()
