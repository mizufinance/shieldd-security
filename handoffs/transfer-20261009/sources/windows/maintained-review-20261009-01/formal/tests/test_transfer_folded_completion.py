"""Exact one-write folded quotient recipes, without invented product rows."""
import unittest
from circuits import transfer_arithmetic as arithmetic
from circuits.transfer_balance_rows import combine,canonical


class FoldedCompletionTests(unittest.TestCase):
    def fixture(self):
        numerator=((12,9),(15,1));quotient=((16,1),)
        certificate=dict(kind='folded',coefficient=1,output=quotient,rows=[31],
                         numerator=numerator,denominator=((0,1),),quotient=quotient)
        return certificate,{31:(combine(quotient,numerator,-1),())}

    def test_one_captured_pivot_and_assertion_only(self):
        certificate,normalized=self.fixture()
        result=arithmetic.folded_quotient_completion_certificate(certificate,normalized)
        self.assertEqual(result,dict(input=certificate['numerator'],remainder=(),output=16,rows=[31]))
        self.assertNotIn('product',result);self.assertNotIn('auxiliary',result)

    def test_nonunit_denominator_and_nonfresh_pivot_refuse(self):
        certificate,normalized=self.fixture()
        certificate['denominator']=((0,2),)
        self.assertIsNone(arithmetic.folded_quotient_completion_certificate(certificate,normalized))
        certificate,normalized=self.fixture();certificate['numerator']=((16,1),)
        self.assertIsNone(arithmetic.folded_quotient_completion_certificate(certificate,normalized))

    def test_changed_row_or_reversed_orientation_refuses_exact_transport(self):
        certificate,normalized=self.fixture();normalized[31]=((),())
        self.assertIsNone(arithmetic.folded_quotient_completion_certificate(certificate,normalized))
        certificate,normalized=self.fixture();a,b=normalized[31]
        normalized[31]=(canonical((column,-coefficient) for column,coefficient in a),b)
        self.assertIsNone(arithmetic.folded_quotient_completion_certificate(certificate,normalized))


if __name__=='__main__':unittest.main()
