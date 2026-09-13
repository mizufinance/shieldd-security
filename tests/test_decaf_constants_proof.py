import unittest

from decaf_constants_proof import certificate_rejected, validate_fields


class ConstantsAcceptanceTests(unittest.TestCase):
    def test_both_field_identities_are_required(self):
        validate_fields({"fields": {"fq": "17", "fr": "19"}})
        for fields in ({}, {"fq": "17"}, {"fr": "19"},
                       {"fq": "17", "fr": "19", "fp": "23"}):
            with self.subTest(fields=fields), self.assertRaises(ValueError):
                validate_fields({"fields": fields})

    def test_rejection_requires_exact_mutant_and_checker_failure(self):
        diagnostic = 'File "fqMutant.v", line 12, characters 0-10:\nError: Unable to unify "true" with "false".'
        failure = "verification process failed (1); see log"
        self.assertTrue(certificate_rejected(diagnostic, "fqMutant.v", failure))
        self.assertTrue(certificate_rejected(diagnostic.replace('"fqMutant.v"', '"./fqMutant.v"'), "fqMutant.v", failure))
        for rejected_run in ("timeout", "interrupted", "verification process failed (-9); see log", "verification process failed (137); see log"):
            self.assertFalse(certificate_rejected(diagnostic, "fqMutant.v", rejected_run))
        for changed in (diagnostic.replace("fqMutant.v", "frMutant.v"),
                        diagnostic.replace("fqMutant.v", "OtherfqMutant.v"),
                        diagnostic.replace("fqMutant.v", "fqMutantXv"),
                        diagnostic.replace('Unable to unify "true" with "false"', "Missing dependency"),
                        diagnostic.replace('Error:', 'Warning:') + '\nError: Unable to unify "true" with "false".',
                        'Error: Unable to unify "true" with "false".'):
            with self.subTest(diagnostic=changed):
                self.assertFalse(certificate_rejected(changed, "fqMutant.v", failure))


if __name__ == "__main__":
    unittest.main()
