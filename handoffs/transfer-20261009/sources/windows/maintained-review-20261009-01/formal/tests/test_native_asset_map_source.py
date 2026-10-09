"""Owned literal map source/contract and deferred guard wiring; no compiler."""
import ast,hashlib,json,re,unittest
from pathlib import Path
R=Path('C:/src/shieldd-formal')
P=R/'.work/diagnostics/transfer-implementation-20261002'

class NativeAssetMapSourceTests(unittest.TestCase):
    def test_named_primitives_and_actual_source_preserve_exceptional_identity(self):
        source=(R/'circuits/ShielddSecurity/NativeAssetMap.lean').read_text()
        sdk=Path('C:/src/shieldd-pr160-844389ee/crates/crypto/primitives/src/map.rs').read_text()
        for operation in ['let k = -Fq::from(40964);','let c1 = Fq::from(40962) * inverse;',
                          'let c2 = inverse.square();','let tv = Fq::from(5) * u.square();',
                          'let zero = !inverse.is_some();','inverse.unwrap_or(Fq::ZERO)',
                          'y.to_bytes()[0] & 1','from_raw_unchecked(x, y)).clear_cofactor()']:
            self.assertIn(operation,sdk)
        self.assertIn('if (ops.invert denominator).isSome then',source)
        self.assertIn('else ops.natural 1',source)
        self.assertIn('points.clear (points.raw p.1 p.2)',source)
        self.assertIn('Group.OnCurve d',source)
        self.assertNotIn('mapMeaning',source)
        self.assertNotIn('firstNonzero',source)
        self.assertNotRegex(source,r'\b(sorry|admit|native_decide|axiom)\b')
        checks=re.findall(r'^#check @([\w.]+)',source,re.M)
        self.assertEqual(checks,re.findall(r'^#print axioms ([\w.]+)',source,re.M))
        self.assertEqual(len(checks),9)
        self.assertEqual(source.count('set_option pp.all true in'),9)
        self.assertIn('variable {F Q : Type} [Field F] [DecidableEq F]',source)
        primitive_laws=source[source.index('  zeroValue :'):source.index('variable (fq :')]
        self.assertNotIn('value fq',primitive_laws)
        self.assertIn('value (F := F) fq zero = 0',primitive_laws)
        self.assertIn('(invert a).map (value (F := F) fq)',primitive_laws)

    def test_frozen_root_route_binds_source_and_passed_same_object_dependencies(self):
        packet=P/'native-asset-map-source-04'
        summary=json.loads((packet/'summary.json').read_bytes())
        self.assertEqual(summary['modules'],{'NativeAssetMap':9})
        self.assertIs(summary['qualification'],False)
        for rel,digest in summary['files'].items():
            self.assertEqual(hashlib.sha256((packet/rel).read_bytes()).hexdigest(),digest)
        for raw,digest in summary['inputs'].items():
            self.assertEqual(hashlib.sha256(Path(raw).read_bytes()).hexdigest(),digest)
        driver=(P/'prepare-native-asset-map-kernel-05.py').read_text()
        compile(driver,str(P/'prepare-native-asset-map-kernel-05.py'),'exec')
        sdk_audit=json.loads((P/'narrow-native-adapters-03-kernel/ShielddNativeSdk/audit.json').read_bytes())
        self.assertEqual(len(sdk_audit['names']),9)
        self.assertIn("leaf('narrow-native-adapters-03-kernel','ShielddNativeSdk',9)",driver)
        self.assertIn("leaf('narrow-asset-downstream-root-interop-09-kernel','ElligatorNativeRootInterop',4)",driver)
        self.assertIn("if '--publish'not in sys.argv",driver)
        self.assertNotIn('relation.jsonl',driver)
        guard=(P/'prepare-native-asset-map-kernel-05.ps1').read_text()
        self.assertIn(hashlib.sha256((P/'prepare-native-asset-map-kernel-05.py').read_bytes()).hexdigest(),guard)
        self.assertIn(hashlib.sha256((packet/'summary.json').read_bytes()).hexdigest(),guard)
        self.assertIn('PrivateMemorySize64 -gt 134217728',guard)
        self.assertIn('.TotalSeconds -ge 120',guard)
