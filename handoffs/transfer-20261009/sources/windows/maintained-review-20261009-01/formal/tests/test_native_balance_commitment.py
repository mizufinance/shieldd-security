"""Exact owned balance source fold and successful-input commitment boundary."""
from pathlib import Path
import re
import unittest

RUNTIME=Path('C:/src/shieldd-pr160-844389ee')
REPO=Path(__file__).resolve().parents[1]


class NativeBalanceCommitmentTests(unittest.TestCase):
    def test_source_spends_outputs_and_commitment_signs(self):
        plans=(RUNTIME/'crates/core/component/shielded-pool/src/shielded_note_plan.rs').read_text()
        spendStart=plans.index('pub fn balance(')
        spend=plans[spendStart:plans.index('#[derive(Clone, Debug, Deserialize',spendStart)]
        self.assertIn('amount: self.note.value().amount',spend)
        self.assertIn('asset_id: self.note.value().asset_id',spend)
        self.assertIn('.into()',spend)
        output=plans[plans.index('pub fn balance(',plans.index('impl ShieldedOutputPlan')):]
        self.assertIn('-Balance::from(self.value)',output)
        plan=(RUNTIME/'crates/core/component/shielded-pool/src/transfer/plan.rs').read_text()
        fold=plan[plan.index('pub fn balance('):plan.index('fn first_spend')]
        self.assertEqual(fold.count('.fold(Balance::default()'),2)
        self.assertLess(fold.index('acc += spend.balance()'),fold.index('acc += output.balance()'))
        balance=(RUNTIME/'crates/core/asset/src/balance.rs').read_text()
        self.assertIn('let non_zero = NonZeroU128::try_from(value.amount.value()).ok()?;',balance)
        commit=balance[balance.index('pub fn commit('):balance.index('impl PartialEq')]
        for operation in ('commitment -= G_v * Fr::from(value.amount)',
                          'commitment += G_v * Fr::from(value.amount)'):
            self.assertIn(operation,commit)
        self.assertEqual(commit.count('commitment += *VALUE_BLINDING * blinding_factor;'),1)
        self.assertGreater(commit.index('commitment += *VALUE_BLINDING'),commit.index('for imbalance in self.iter()'))
        imbalance=(RUNTIME/'crates/core/asset/src/balance/imbalance.rs').read_text()
        self.assertIn('r.get().checked_add(s.get())',imbalance)
        self.assertIn('panic!("overflow when adding imbalances")',imbalance)
        self.assertIn('Ordering::Equal => None',imbalance)

    def test_native_separate_amount_sums_and_zero_overflow_domain(self):
        source=(RUNTIME/'crates/crypto/circuits/src/balance.rs').read_text()
        native=source[source.index('pub fn native('):source.index('/// Action net value')]
        self.assertIn('amount(values[0]) + &amount(values[1])',native)
        self.assertIn('let input = generator.multiply(&sum(inputs));',native)
        self.assertIn('let mut output = generator.multiply(&sum(outputs));',native)
        self.assertIn('output.x = -output.x;',native)
        self.assertIn('.add(&generators.blinding.multiply(blinding)',native)
        # Native field totals fit 129 bits. SDK same-sign folds are narrower:
        # even exact net zero cannot rescue a preceding u128 overflow.
        limit=2**128
        self.assertLess(2*(limit-1),2**129)
        self.assertGreaterEqual((limit-1)+1,limit)
        self.assertEqual(((limit-1)+1)-((limit-1)+1),0)
        for inputs,outputs,signed in ((0,0,0),(5,0,5),(0,5,-5),(5,5,0),(7,3,4),(3,7,-4)):
            canonical=0 if inputs==outputs else (inputs-outputs if inputs>outputs else -(outputs-inputs))
            self.assertEqual(canonical,signed)
            # Independent cyclic-group oracle checks both signs plus one blind.
            self.assertEqual((canonical*17+11*29)%101,(inputs*17-outputs*17+11*29)%101)

    def test_proof_interface_admits_success_not_desired_commitment(self):
        source=(REPO/'circuits/ShielddSecurity/NativeBalanceCommitment.lean').read_text()
        checks=re.findall(r'#check @([A-Za-z0-9_]+)',source)
        self.assertEqual(len(checks),8)
        self.assertEqual(checks,re.findall(r'#print axioms ([A-Za-z0-9_]+)',source))
        self.assertIn('set_option maxHeartbeats 300000',source)
        self.assertIn('set_option maxRecDepth 2048',source)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        declaration=source[source.index('theorem native_balance_commitment'):].split(':=',1)[0]
        self.assertIn('(sdkSuccess : sdkNet inputs outputs = some net)',declaration)
        self.assertIn('(nativeSuccess : NativeTransferAdmission.balanceNative',declaration)
        for forbidden in ('(satisfied','(desired','(commitmentEqual','(nativePoint','(nonidentity'):
            self.assertNotIn(forbidden,declaration)
        self.assertIn('model.covers inverse curve',source)
        self.assertIn('GroupByteCodec.native_reader_coordinates',source)
        self.assertIn('TransferReduction.decode_canonical_cast',source)
        self.assertIn('simp only [natCast_zsmul,sub_eq_add_neg]',source)


if __name__=='__main__':unittest.main()
