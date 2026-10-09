"""Static root-guard wiring checks; no WSL/Cargo/production stream is run."""
import hashlib,json,unittest
from pathlib import Path

P=Path(__file__).parents[1]/'.work/diagnostics/transfer-implementation-20261002'


class BlindingRecipeTests(unittest.TestCase):
    def test_frozen_source_and_all_guard_inputs_are_exact(self):
        recipe=json.loads((P/'balance-blinding-root-recipes-01.json').read_bytes())
        self.assertEqual(recipe['status'],'ALL UNRUN');self.assertIs(recipe['qualification'],False)
        self.assertEqual(recipe['new_blinding_pages'],8);self.assertEqual(recipe['schemas_preserved'],{'epk':48,'balance_variable':5})
        for raw,digest in recipe['inputs'].items():
            with self.subTest(path=raw):self.assertEqual(hashlib.sha256(Path(raw).read_bytes()).hexdigest(),digest)
        m=json.loads((P/'balance-blinding-observer-source-02/manifest.json').read_bytes())
        self.assertEqual(len(m['changed']),6)
        for rel,digest in m['files'].items():self.assertEqual(hashlib.sha256((P/'balance-blinding-observer-source-02'/rel).read_bytes()).hexdigest(),digest)

    def test_one_build_three_native_filters_shared_binary_and_original_shapes(self):
        recipe=json.loads((P/'balance-blinding-root-recipes-01.json').read_bytes());order=recipe['serial_order']
        self.assertEqual(order[0],'balance-variable-freeze-parent-01')
        self.assertEqual(sum('build-guard' in name for name in order),1)
        build=(P/'epk-all-build-guard-04.sh').read_text()
        for unit in ['epk-all-unit-guard-04','epk-all-balance-unit-04','balance-blinding-unit-guard-01']:
            self.assertLess(order.index(unit),order.index('epk-all-build-guard-04'))
            self.assertIn(unit+'/wrapper-exit.txt',build);self.assertIn(unit+'/stop.txt',build)
        self.assertIn('cargo rustc -vv --locked',build);self.assertIn('-- --cfg shieldd_formal_example',build)
        self.assertNotIn('C:\\src',build);self.assertNotIn('RUSTFLAGS',build)
        for kind,mode in [('epk-all','epk-all-fixed-pages-spool'),('balance-variable','balance-variable-pages-spool'),('balance-blinding','balance-blinding-fixed-pages-spool')]:
            suffix='04' if kind=='epk-all' else '03' if kind=='balance-variable' else '01'
            first=(P/f'{kind}-first-{suffix}.sh').read_text();qualifier=(P/f'{kind}-qualify-{suffix}.sh').read_text()
            self.assertIn(recipe['private_binary']+'/transfer-ownership-inspection',first)
            self.assertIn(recipe['child'],first);self.assertIn(mode,first)
            self.assertIn('epk-all-build-guard-04/frozen-binary.sha256',first)
            self.assertIn('epk-all-stage-guard-04/final-inventory.sha256',first)
            self.assertIn('epk-all-ordinary1-04/capture',qualifier);self.assertIn('epk-all-ordinary2-04/capture',qualifier)
            self.assertIn(f'{kind}-first-{suffix}/capture',qualifier);self.assertIn(f'{kind}-repeat-{suffix}/capture',qualifier)
            self.assertIn('1572864',first);self.assertIn('524288',first)

    def test_actual_parent_inventory_is_required_before_six_new_writes(self):
        stage=(P/'balance-blinding-observer-source-02/lib/integration/balance_blinding_stage.py').read_text()
        self.assertLess(stage.index('complete actual parent inventory changed'),stage.index('receipt.mkdir()'))
        self.assertLess(stage.index('pure hook composition differs'),stage.index('shutil.copytree(parent,child)'))
        self.assertIn('inventory(parent)!=before',stage)
        guard=(P/'epk-all-stage-guard-04.sh').read_text()
        self.assertIn('balance-blinding-observer-source-02/stage.py',guard)
        self.assertNotIn('stage.py balance-sibling',guard)
        unit=(P/'balance-blinding-unit-guard-01.sh').read_text()
        self.assertIn('group::balance_blinding_fixed_inspection::tests -- --nocapture',unit)
        self.assertNotIn('group::epk_fixed_inspection::tests',unit)


class LfBlindingRecipeTests(unittest.TestCase):
    def test_every_executable_shell_and_cleanup_is_exact_lf(self):
        recipe=json.loads((P/'balance-blinding-root-recipes-02.json').read_bytes())
        self.assertEqual(len(recipe['shell_bytes']),41)
        self.assertIn('UNRUN bash -n',recipe['executable_shell_validation'])
        for entry in recipe['shell_bytes']:
            data=Path(entry['path']).read_bytes()
            self.assertNotIn(b'\r',data);self.assertEqual(entry['cr_bytes'],0)
            self.assertEqual(hashlib.sha256(data).hexdigest(),entry['sha256'])
        for raw,digest in recipe['inputs'].items():self.assertEqual(hashlib.sha256(Path(raw).read_bytes()).hexdigest(),digest)
        # Retained defective templates remain recoverable; this is a byte-level
        # source test, not Bash parse/runtime qualification/control credit.
        self.assertIn(b'\r\n',(P/'epk-all-build-guard-04.sh').read_bytes())

    def test_fresh_parent_association_and_three_capture_siblings(self):
        recipe=json.loads((P/'balance-blinding-root-recipes-02.json').read_bytes())
        m=json.loads((P/'balance-blinding-observer-source-03/manifest.json').read_bytes())
        self.assertEqual(m['required_guards'],['balance-variable-freeze-parent-01','epk-parent-stage-guard-01'])
        self.assertEqual(m['child'],recipe['child']);self.assertEqual(m['receipt'],'balance-blinding-stage-02')
        stage=(P/'epk-all-stage-guard-05.sh').read_text()
        self.assertIn('balance-blinding-observer-source-03/stage.py',stage)
        self.assertIn('epk-fixed-activation-source-02/stage.py balance-sibling',(P/'epk-parent-stage-guard-01.sh').read_text())
        for kind,suffix in [('epk-all','05'),('balance-variable','04'),('balance-blinding','02')]:
            first=(P/f'{kind}-first-{suffix}.sh').read_text();qualifier=(P/f'{kind}-qualify-{suffix}.sh').read_text()
            self.assertIn(recipe['private_binary'],first);self.assertIn(recipe['child'],first)
            self.assertIn('epk-all-build-guard-05/frozen-binary.sha256',first)
            self.assertIn('epk-all-ordinary1-05/capture',qualifier);self.assertIn('epk-all-ordinary2-05/capture',qualifier)
            self.assertIn(f'{kind}-first-{suffix}/capture',qualifier);self.assertIn(f'{kind}-repeat-{suffix}/capture',qualifier)
