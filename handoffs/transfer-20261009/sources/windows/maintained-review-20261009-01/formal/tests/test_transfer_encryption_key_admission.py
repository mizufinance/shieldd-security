"""Typed synthetic source controls; no actual capture or proof qualification."""
import copy
import io
import re
import unittest
from circuits import generate_transfer_encryption_key_admission as renderer
from circuits import transfer_encryption_registered_guard as guard
from circuits.transfer_encryption_dh_keys import infer_regulated_selectors
from circuits.transfer_balance_rows import combine
from circuits.transfer_relation import MODULUS, RelationError
from tests.test_transfer_encryption_registered_guard import fixture as guard_fixture


def fixture():
    checked,data = guard_fixture()
    for axis,value in enumerate(v for point in renderer.FIXED for v in point):
        for offset,coefficient in ((0,value),(1,(-value)%MODULUS)):
            handle = (0,2*axis+offset)
            checked['expressions'][handle] = checked['derived'][handle] = ((0,coefficient),)
    for handle,(multiply,left,right) in sorted(checked['nodes'].items()):
        checked['derived'][handle] = (((200+handle[1],1),) if multiply else
            combine(checked['derived'][left],checked['derived'][right]))
    selectors = infer_regulated_selectors(checked)
    cofactors = dict(selectors=selectors,cofactors=[
        dict(namespace='RuntimeTransferEncryptionLeaf'+label+'Subgroup',
            point=tuple(checked['derived'][h[1]] for h in selectors['selectors'][key]['leaf']))
        for label,key in (('Detection','detection_key'),('Payload','payload_key'))])
    extracted = guard.extract(checked,lambda:io.BytesIO(data))
    return checked,cofactors,extracted


class EncryptionKeyAdmissionTests(unittest.TestCase):
    def test_owned_fixed_coordinates_actual_roles_and_nonidentity_are_conclusions(self):
        checked,cofactors,extracted = fixture()
        name,source = renderer.generate(checked,cofactors,extracted)
        self.assertEqual(name,'RuntimeTransferEncryptionKeyAdmission')
        audits = re.findall(r'^#check @([\w.]+)$',source,re.M)
        self.assertEqual(len(audits),7)
        self.assertEqual(audits,re.findall(r'^#print axioms ([\w.]+)$',source,re.M))
        self.assertIn('private def rowModel',source)
        self.assertIn('coordinates := model.coordinates',source)
        self.assertIn('RuntimeNativeEncryptionInitializationCoefficients.d_value',source)
        self.assertIn('NativeEncryptionFixedAdmission.represented_keys',source)
        self.assertIn('RuntimeTransferEncryptionDetectionInverse.represented_nonidentity',source)
        self.assertIn('RuntimeTransferEncryptionRegisteredPayloadGuard.represented_nonidentity',source)
        # The literal y coefficients exceed p/2 and are emitted as negative
        # integers by the shared row renderer. Congruence needs a checked cast.
        self.assertIn(str(renderer.FIXED[0][1]-MODULUS)+' : Int',source)
        self.assertIn('polynomial_certificate',source)
        signature = source.split('theorem represented_selected_keys',1)[1].split(':= by',1)[0]
        premises = signature.split(':\n    ∃ detection payload',1)[0]
        for forbidden in ('fallbackRole','baseRole','leafRole','nonidentity','detection ≠','payload ≠'):
            self.assertNotIn(forbidden,premises)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom|native_decide)\b')

    def test_valid_selector_with_wrong_fixed_key_is_refused(self):
        checked,cofactors,extracted = fixture()
        for handle,coefficient in (((0,0),19),((0,1),MODULUS-19)):
            checked['expressions'][handle] = checked['derived'][handle] = ((0,coefficient),)
        for handle,(multiply,left,right) in sorted(checked['nodes'].items()):
            checked['derived'][handle] = (((200+handle[1],1),) if multiply else
                combine(checked['derived'][left],checked['derived'][right]))
        cofactors['selectors'] = infer_regulated_selectors(checked)
        with self.assertRaisesRegex(RelationError,'fallback differs'):
            renderer.generate(checked,cofactors,extracted)

    def test_foreign_point_flag_rows_or_cofactor_binding_is_refused(self):
        checked,cofactors,extracted = fixture()
        for mutation in ('point','flag','row','cofactor'):
            original = copy.deepcopy(extracted)
            cofactor = copy.deepcopy(cofactors)
            if mutation=='point':
                original['point'] = (((8,1),),((9,1),))
            elif mutation=='flag':
                original['flag'] = ((4,1),)
            elif mutation=='row':
                original['selected_rows'][0]['a'] = [[0,'0'*63+'1']]
            else:
                cofactor['cofactors'][1]['point'] = (((4,1),),((5,1),))
            with self.subTest(mutation=mutation),self.assertRaises(RelationError):
                renderer.generate(checked,cofactor,original)

    def test_pending_foreign_schema_nonfirst_and_boolean_roles_are_refused(self):
        checked,cofactors,extracted = fixture()
        for mutation in ('pending','schema','role','boolean'):
            current = copy.deepcopy(checked)
            if mutation=='pending':
                current['qualified']=False
            elif mutation=='schema':
                current['metadata']['schema']='shieldd-transfer-ownership-v1'
            else:
                current['metadata']['role']=False if mutation=='boolean' else 1
            with self.subTest(mutation=mutation),self.assertRaises(RelationError):
                renderer.generate(current,cofactors,extracted)
