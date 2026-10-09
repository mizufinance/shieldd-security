"""Pinned independent native-success admission and its honest zero exception."""
from pathlib import Path
import re
import unittest

RUNTIME=Path('C:/src/shieldd-pr160-844389ee')
REPO=Path(__file__).resolve().parents[1]


class NativeTransferAdmissionTests(unittest.TestCase):
    def test_pinned_statement_evaluation_propagates_native_balance_rejection(self):
        balance=(RUNTIME/'crates/crypto/circuits/src/balance.rs').read_text()
        native=balance[balance.index('pub fn native('):balance.index('/// Action net value')]
        anchors=['"noncanonical balance blinding"','let generator = map::asset(params, asset);',
                 'generator != Point::identity()', '"asset generator is identity"',
                 'let input = generator.multiply(&sum(inputs));']
        self.assertEqual([native.index(a) for a in anchors],sorted(native.index(a) for a in anchors))
        self.assertIn(') -> Result<Point<Scalar>>',native)
        transfer=(RUNTIME/'crates/crypto/circuits/src/transfer.rs').read_text()
        statement=transfer[transfer.index('pub fn statement('):transfer.index('/// Returns the sole public')]
        self.assertIn(') -> Result<Statement<Scalar>>',statement)
        self.assertIn('balance: balance::native(',statement)
        self.assertIn('&w.balance_blinding,\n        )?',statement)
        catalogue=(RUNTIME/'crates/crypto/circuits/src/catalogue.rs').read_text()
        digest=catalogue[catalogue.index('pub fn digest('):catalogue.index('pub fn constrain')]
        self.assertIn('&transfer::statement(p, g, w)?.fields()',digest)
        evaluate=catalogue[catalogue.index('pub fn evaluate('):catalogue.index('\nfn zero()')]
        self.assertLess(evaluate.index('witness.digest(&p, &g)?'),evaluate.index('build_with_values'))
        primitive=(RUNTIME/'crates/crypto/primitives/src/map.rs').read_text()
        self.assertIn('pub fn to_subgroup(u: &Fq) -> SubgroupPoint',primitive)
        self.assertIn('.clear_cofactor()',primitive)
        self.assertNotIn('ensure!',primitive)
        self.assertNotRegex(primitive,r'\b(retry|remap)\b')
        asset=(RUNTIME/'crates/core/asset/src/asset/id.rs').read_text()
        generator=asset[asset.index('pub fn value_generator('):asset.index('/// Convert the asset ID')]
        self.assertIn('domains::ASSET_GENERATOR',generator)
        self.assertNotIn('ensure!',generator)

    def test_handwritten_guard_derives_inverse_from_native_success_and_global_order(self):
        source=(REPO/'circuits/ShielddSecurity/NativeTransferAdmission.lean').read_text()
        names=re.findall(r'#check @([A-Za-z0-9_]+)',source)
        self.assertEqual(len(names),6)
        self.assertEqual(names,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        for theorem in ('balance_success_nonidentity','successful_cofactor_x','successful_cofactor_inverse'):
            declaration=source[source.index('theorem '+theorem):]
            declaration=declaration[:declaration.index(':=')]
            self.assertIn('(accepted : balanceNative',declaration)
            for forbidden in ('(nonidentity','(desired','(satisfied','(inverseEquation','(nativeAsset'):
                self.assertNotIn(forbidden,declaration)
        self.assertIn('GroupNativeNonidentity.subgroup_nonidentity_x',source)
        self.assertIn('∀ point : J, (8 * Scalar.order) • point = 0',source)
        self.assertIn('set_option maxHeartbeats 250000',source)
        self.assertIn('Bool.and_eq_true_iff.mp checked',source)
        self.assertNotIn('Bool.and_eq_true.mp',source)
        self.assertIn('change model.coordinates (8 • nativeImage asset)',source)


if __name__=='__main__':unittest.main()
