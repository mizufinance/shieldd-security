"""The native signed interpretation uses the actual checked constructor inputs."""
import json,re,unittest
from pathlib import Path
from circuits import generate_transfer_signed_balance_native as native
from circuits import transfer_relation as relation

ROOT=Path(__file__).resolve().parents[1]
PACKET=ROOT/'.work/diagnostics/transfer-implementation-20261002/signed-balance-actual-completion-source-03'


class SignedBalanceNativeTests(unittest.TestCase):
    def test_actual_recipe_signature_and_constructed_columns(self):
        recipe=json.loads((PACKET/'recipe.json').read_bytes())
        name,source=native._from_checked(recipe)
        self.assertEqual(name,'RuntimeTransferSignedBalanceNative')
        self.assertIn('completeAssignment rho amounts 21711 =',source)
        self.assertIn('completeAssignment rho amounts 21712 =',source)
        self.assertIn('original_rows_complete rho amounts one linked nativeAmounts',source)
        self.assertIn('TransferSignedBalanceNative.inputPair amounts',source)
        self.assertEqual(source.count('#check @'),1)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')
        declaration=source.split('theorem constructed_native_result',1)[1].split(':=',1)[0]
        for forbidden in ('(signed :','(nonidentity','(desired','(satisfied','(pointEqual'):
            self.assertNotIn(forbidden,declaration)
        damaged=dict(recipe,selected_expression=[[recipe['magnitude'],1]])
        with self.assertRaises(relation.RelationError):native._from_checked(damaged)

    def test_signed_native_groups_and_sdk_domain_remain_distinct(self):
        limit=2**128
        cases=((0,0,0,0),(1,2,4,5),(4,5,1,2),(limit-1,limit-1,0,0),
               (0,0,limit-1,limit-1),(limit-1,1,limit-1,1))
        for a,b,c,d in cases:
            signed=a+b-c-d
            magnitude=abs(signed)
            scalar=-magnitude if a+b<c+d else magnitude
            self.assertEqual(scalar,signed)
            self.assertLess(magnitude,2**129)
            self.assertEqual((scalar*17+11*29)%101,((a+b)*17-(c+d)*17+11*29)%101)
        self.assertEqual(sum(cases[-1][:2])-sum(cases[-1][2:]),0)
        self.assertFalse(sum(cases[-1][:2])<limit)  # SDK fold still panics.
        helper=(ROOT/'circuits/ShielddSecurity/TransferSignedBalanceNative.lean').read_text()
        self.assertEqual(re.findall(r'#check @(\w+)',helper),re.findall(r'#print axioms (\w+)',helper))
        self.assertEqual(helper.count('#check @'),3)
        self.assertIn('sdk_net_success',helper)
        self.assertIn('native_balance_commitment',helper)


if __name__=='__main__':unittest.main()
