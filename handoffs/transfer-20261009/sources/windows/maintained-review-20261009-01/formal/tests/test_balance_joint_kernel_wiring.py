"""Actual source packet wiring only: no replay, candidate generation or kernel."""
from pathlib import Path
import hashlib,json,re,unittest
P=Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')

class BalanceJointKernelWiringTests(unittest.TestCase):
    def test_actual_result_format_and_input_binding(self):
        actual=P/'balance-joint-actual-13'
        receipt=json.loads((actual/'receipt.json').read_bytes())
        self.assertTrue((actual/'complete.txt').is_file())
        self.assertFalse((actual/'summary.json').exists())
        self.assertEqual((receipt['ordinary_replays'],receipt['parent_ordinary_replays']),(0,1))
        inventory=json.loads((actual/'module-inventory.json').read_bytes())
        self.assertEqual(len(inventory),1373)
        record=inventory['RuntimeBalanceInputLayout']
        raw=(actual/'modules/RuntimeBalanceInputLayout.lean').read_bytes()
        self.assertEqual(hashlib.sha256(raw).hexdigest(),record['sha256'])
        checks=re.findall(r'^#check @([\w.]+)',raw.decode(),re.M)
        imports=re.findall(r'^import ShielddSecurity\.([\w.]+)\s*$',raw.decode(),re.M)
        self.assertEqual(['ShielddSecurity.'+name for name in imports],record['imports'])
        self.assertEqual(checks,record['full_signatures'])
        self.assertEqual(checks,record['axiom_commands'])
        self.assertEqual(len(checks),6)
        # This actual source constructor derives 9=2; no input equality premise.
        self.assertIn('constructs (base : Nat → F)',raw.decode())
        self.assertNotIn('base 9 = base 2 →',raw.decode())

    def test_bounded_root_route_requires_audited_imports_and_exact_body(self):
        driver=(P/'prepare-balance-joint-kernel-03.py').read_bytes()
        compile(driver,str(P/'prepare-balance-joint-kernel-03.py'),'exec')
        text=driver.decode()
        for obligation in ['external_leaf','len(selected)<=24','actual_parent_flags_unchanged=True',
                           'source_receipt()',"checks==audits==record['full_signatures']",'No generated source edits allowed']:
            self.assertIn(obligation,text)
        self.assertNotIn('relation.jsonl',text)
        self.assertIn("['ShielddSecurity.'+dep for dep in imports]==record['imports']",text)
        self.assertIn("audit['names'] in (names,references)",text)
        recipe=json.loads((P/'balance-joint-kernel-root-recipe-03.json').read_bytes())
        self.assertEqual(hashlib.sha256(driver).hexdigest(),recipe['prepare_driver_sha256'])
        guard=(P/'prepare-balance-joint-kernel-03.ps1').read_bytes()
        self.assertEqual(hashlib.sha256(guard).hexdigest(),recipe['prepare_guard_sha256'])
        self.assertIn('PrivateMemorySize64 -gt 536870912',guard.decode())
        self.assertFalse(recipe['qualification'])

    def test_exact_template_copies_actual_bytes_without_signature_injection(self):
        path=P/'prepare-exact-source-kernel-01.py'
        text=path.read_text();compile(text,str(path),'exec')
        self.assertIn('target.write_bytes(path.read_bytes())',text)
        self.assertIn('assert checks==prints',text)
        self.assertNotIn('body=body.replace(ending',text)
        recipe=json.loads((P/'balance-joint-kernel-root-recipe-03.json').read_bytes())
        self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),recipe['exact_source_template_sha256'])

    def test_sparse_layout_render_changes_only_scalar_import(self):
        from circuits import transfer_balance_input_layout as layout
        actual=P/'balance-joint-actual-13'
        extraction=json.loads((actual/'extraction.json').read_bytes())
        name,body=layout.render(extraction['input_layout'])
        old=(actual/'modules'/(name+'.lean')).read_text()
        self.assertEqual(body,old.replace('import ShielddSecurity.CompilerSignedCompletion\n',
            'import ShielddSecurity.CompilerSignedCompletion\nimport ShielddSecurity.Scalar\n',1))
        self.assertEqual(re.findall(r'^#check @([\w.]+)',body,re.M),
                         ['outside','value','canonical_complete','raw_checked','constructs','binding'])
        producer=P/'balance-layout-producer-04'
        manifest=json.loads((producer/'manifest.json').read_bytes())
        for relative,digest in manifest['files'].items():
            self.assertEqual(hashlib.sha256((producer/relative).read_bytes()).hexdigest(),digest)
        compile((P/'prepare-balance-layout-kernel-04.py').read_bytes(),'actual-sparse-layout-driver','exec')

    def test_scalar_reuse_is_exact_watched_dependency_not_theorem_audit(self):
        path=P/'prepare-balance-layout-kernel-05.py'
        namespace={'__name__':'fixture_only','__file__':str(path)}
        exec(compile(path.read_bytes(),str(path),'exec'),namespace)
        batch=P/'narrow-linear-mixed-02-kernel'
        parent=dict(module='CompilerLinearCompletion',exports=2,batch=str(batch))
        watched={}
        def watch(path):
            path=Path(path).resolve()
            self.assertTrue(path.is_file())
            watched[str(path)]=hashlib.sha256(path.read_bytes()).hexdigest()
            return path
        def data(path,limit):
            self.assertLessEqual(Path(path).stat().st_size,limit)
            watch(path)
            return json.loads(Path(path).read_bytes())
        ns=dict(watch=watch,data=data,read=lambda path:watch(path).read_text())
        receipt=namespace['watched_scalar_dependency'](ns,parent)
        self.assertEqual(receipt['exports'],0)
        self.assertFalse(receipt['direct_theorem_audit'])
        self.assertEqual(receipt['qualified_parent'],parent)
        self.assertIn(str((namespace['STAGE']/'Scalar.olean').resolve()),
                      receipt['watched_dependencies'])
        self.assertIn(str((namespace['STAGE']/'Arithmetic.lean').resolve()),
                      receipt['watched_dependencies'])
        original=data
        def changed(path,limit):
            result=original(path,limit)
            if Path(path).name=='dependencies-after.json':
                result=[dict(row,sha256='0'*64) if row['path'].endswith('Scalar.olean') else row
                        for row in result]
            return result
        with self.assertRaisesRegex(AssertionError,'Watched dependency changed'):
            namespace['watched_scalar_dependency'](dict(ns,data=changed),parent)
        with self.assertRaises(AssertionError):
            namespace['watched_scalar_dependency'](ns,dict(parent,exports=0))
        recipe=json.loads((P/'balance-layout-kernel-root-recipe-05.json').read_bytes())
        self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),recipe['prepare_driver_sha256'])
        guard=P/'prepare-balance-layout-kernel-05.ps1'
        self.assertEqual(hashlib.sha256(guard.read_bytes()).hexdigest(),recipe['prepare_guard_sha256'])
        self.assertIn(recipe['prepare_driver_sha256'],guard.read_text())

    def test_joint_slice_route_keeps_original_inventory_and_qualified_override(self):
        path=P/'prepare-balance-joint-kernel-04.py'
        body=path.read_text();compile(body,str(path),'exec')
        for obligation in ['len(selected)<=24','unchanged_other_modules',
                           "layout_receipt['exports']==6",'current.read_bytes()==sparse_source.read_bytes()',
                           "external={layout:layout_receipt}","'narrow-balance-joint-input-layout-05-kernel'",
                           "checks==audits==record['full_signatures']"]:
            self.assertIn(obligation,body)
        self.assertNotIn('layout.render',body)
        self.assertNotIn('relation.jsonl',body)
        guard=(P/'prepare-balance-joint-kernel-04.ps1').read_text()
        self.assertIn('param([string]$Modules=',guard)
        self.assertIn("'--modules',$Modules,'--name',$Name,'--publish'",guard)
        recipe=json.loads((P/'balance-joint-kernel-root-recipe-04.json').read_bytes())
        self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(),recipe['driver_sha256'])
        self.assertEqual(hashlib.sha256((P/'prepare-balance-joint-kernel-04.ps1').read_bytes()).hexdigest(),recipe['guard_sha256'])
        self.assertEqual(recipe['max_selected_modules'],24)
