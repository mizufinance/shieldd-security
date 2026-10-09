import unittest
from audit_log import validate

NAME='ShielddSecurity.Test.proof'
GOOD=NAME+' : @Eq.{0} Nat Nat.zero Nat.zero\n'+"'"+NAME+"' does not depend on any axioms\n"
class AuditAcceptance(unittest.TestCase):
    def test_zero_axiom_and_full_signature(self):
        self.assertEqual(validate(GOOD,[NAME],[NAME])['axiom_audits'],1)
    def test_standard_axioms(self):
        text=GOOD.replace('does not depend on any axioms','depends on axioms: [propext, Quot.sound, Classical.choice]')
        self.assertEqual(validate(text,[NAME],[NAME])['axiom_audits'],1)
    def test_equal_count_wrong_name(self):
        with self.assertRaises(AssertionError):validate(GOOD.replace(NAME,NAME+'Wrong'),[NAME],[NAME])
    def test_duplicated_named_zero_audit(self):
        with self.assertRaises(AssertionError):validate(GOOD+GOOD,[NAME],[NAME])
    def test_hidden_nonstandard_axiom(self):
        text=GOOD.replace('does not depend on any axioms','depends on axioms: [Classical.choice, maliciousOracle]')
        with self.assertRaises(AssertionError):validate(text,[NAME],[NAME])
    def test_missing_signature(self):
        with self.assertRaises(AssertionError):validate(GOOD.split('\n',1)[1],[NAME],[NAME])
    def test_short_name_refused(self):
        with self.assertRaises(AssertionError):validate(GOOD.replace(NAME,'proof'),['proof'],['proof'])
    def test_error_even_with_matching_census(self):
        with self.assertRaises(AssertionError):validate(GOOD+'error: failed declaration\n',[NAME],[NAME])
    def test_placeholder_even_with_matching_census(self):
        with self.assertRaises(AssertionError):validate(GOOD+'sorryAx\n',[NAME],[NAME])
if __name__=='__main__':unittest.main()
