"""Global codec/admission wrapper generation only; no SDK/runtime evidence."""
import copy
import io
import json
import re
import unittest
from circuits import generate_transfer_rk_sdk as sdk, transfer_rk_subgroup as rk
from tests.test_transfer_rk_subgroup import fixture
from tests.fixed_spend_fixture import full_fixture
from circuits import transfer_fixed_spend as fixed
from circuits.transfer_relation import RelationError


class SdkGenerationTests(unittest.TestCase):
    def setUp(self):
        obj,self.roles,ordinary=fixture();self.data=(json.dumps(obj)+'\n').encode()
        self.extracted=rk.extract(self.data,self.roles,io.BytesIO(ordinary))

    def test_global_reader_admission_and_constructed_public_inputs(self):
        source=sdk.generate(self.data,self.roles,self.extracted)
        self.assertIn('GroupNativeSdk.admissionGate',source)
        self.assertIn('GroupNativeSdk.native_point_read',source)
        self.assertIn('patchAssignment base (publicValues sdk point) publicColumns',source)
        self.assertEqual(source.count('GroupNativeSdk.Sdk (E := E) (S := S) (K := K)'),4)
        statement=source.split('theorem actual_public_key_rows_complete',1)[1].split(':= by',1)[0]
        for premise in ('(inputX','(inputY','(satisfied','(subgroup','(nonidentity'):
            self.assertNotIn(premise,statement)
        audits=re.findall(r'#check @([\w]+)',source)
        self.assertEqual(audits,re.findall(r'#print axioms ([\w]+)',source))
        self.assertEqual(len(audits),3);self.assertEqual(len(set(audits)),3)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom)\b')

    def test_json_roundtrip_is_exact(self):
        self.assertEqual(sdk.generate(self.data,self.roles,self.extracted),sdk.generate(self.data,self.roles,json.loads(json.dumps(self.extracted))))

    def test_changed_owned_public_or_private_allocation_refuses(self):
        changed=copy.deepcopy(self.extracted);changed['allocation']['witnesses'][0]=0
        with self.assertRaises(rk.relation.RelationError):sdk.generate(self.data,self.roles,changed)

    def test_production_randomization_uses_global_reader_and_same_seed(self):
        source=sdk.generate_randomized(self.data,self.roles,self.extracted)
        statement=source.split('theorem actual_randomized_public_rows_complete',1)[1].split(':= by',1)[0]
        for premise in ('(inputX','(inputY','(satisfied','(subgroup','(computedRole'):
            self.assertNotIn(premise,statement)
        self.assertIn('GroupNativeSdk.randomized_native_authorization',source)
        self.assertIn('GroupNativeSdk.scalar_canonical',source)
        self.assertIn('publicBase base sdk randomizedPoint',statement)
        self.assertEqual(source.count('#check @'),4)
        self.assertEqual(source,sdk.generate_randomized(self.data,self.roles,json.loads(json.dumps(self.extracted))))

    def test_owned_programs_construct_sdk_and_decoder_on_same_public_seed(self):
        source=sdk.generate_owned(self.data,self.roles,self.extracted)
        statement=source.split('theorem actual_owned_randomized_public_rows_complete',1)[1].split(':= by',1)[0]
        for premise in ('(sdk :','(decoder :','(inputX','(inputY','(satisfied','(subgroup','(computedRole'):
            self.assertNotIn(premise,statement)
        self.assertIn('ShielddScalarReader.Backend',statement)
        self.assertIn('ShielddNativeSdk.Upstream',statement)
        self.assertIn('publicBase base (ShielddNativeSdk.sdk upstream) randomizedPoint',statement)
        self.assertIn('ShielddNativeAuthorization.production_authorization_agrees',source)
        self.assertIn('ShielddScalarReader.decoder backend',source)
        self.assertEqual(source.count('#check @'),5)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom)\b')
        self.assertEqual(source,sdk.generate_owned(self.data,self.roles,json.loads(json.dumps(self.extracted))))


class OwnedFixedInputTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.captures,cls.roles,ordinary=full_fixture(ordered_fixed=True)
        cls.extractions=[fixed.extract_rows(data,cls.roles,io.BytesIO(ordinary),include_canonical=i==0)
                         for i,data in enumerate(cls.captures)]

    def test_native_read_seed_discharge_bounds_and_meaning_for_all126(self):
        source=sdk.generate_full_owned_inputs(self.captures,self.roles,self.extractions)
        self.assertIn('RuntimeTransferFixedSpendCompletion.actual_rows_complete',source)
        self.assertIn('(fr.bounded randomizer)',source)
        self.assertIn('patchAssignment base (inputValues upstream actionPoint randomizer) inputColumns',source)
        for name in ('owned_seed_reads','owned_fixed_rows_complete','owned_fixed_native_complete'):
            statement=source.split('theorem '+name,1)[1].split(':= by',1)[0]
            for premise in ('(meaning :','(canonical :','(satisfied :','(inputX :','(inputY :','(computedRole :'):
                self.assertNotIn(premise,statement)
        self.assertIn('StandardSpendAuth upstream',source)
        self.assertIn('fixedParameterCoordinates',source)
        self.assertEqual(source.count('#check @'),3)
        self.assertNotRegex(source,r'\b(sorry|admit|axiom)\b')
        self.assertEqual(source,sdk.generate_full_owned_inputs(self.captures,self.roles,
            json.loads(json.dumps(self.extractions))))

    def test_incomplete_coverage_and_folded_or_aliased_inputs_refuse(self):
        with self.assertRaises(RelationError):
            sdk.generate_full_owned_inputs(self.captures[:-1],self.roles,self.extractions[:-1])
        for kind in ('folded','alias'):
            changed=copy.deepcopy(self.roles)
            handle=tuple(changed['metadata']['spend']['ak'][0]['source'])
            scalar=tuple(changed['metadata']['spend']['randomizer']['source'])
            changed['observed'][handle]=((42,2),) if kind=='folded' else changed['observed'][scalar]
            with self.subTest(kind=kind),self.assertRaises(RelationError):
                sdk.generate_full_owned_inputs(self.captures,changed,self.extractions)


if __name__=='__main__':unittest.main()
