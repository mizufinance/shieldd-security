import unittest

from decaf_qualify import classify_control


class QualificationTests(unittest.TestCase):
    def test_negative_controls_require_their_specific_leak(self):
        branch = "[checkct:result] Instruction 0x100 has control flow leak\nProgram status is : insecure"
        address = branch.replace("control flow", "memory access")
        self.assertEqual(classify_control(branch, 1, 0x200)[0], "passed")
        self.assertEqual(classify_control(address, 2, 0x200)[0], "passed")
        self.assertEqual(classify_control(address, 1, 0x200)[0], "blocked")
        self.assertEqual(classify_control(branch, 2, 0x200)[0], "blocked")

    def test_secure_requires_reachable_endpoint_and_complete_analysis(self):
        secure = "[sse:result] Path 1 reached address 0x200\nProgram status is : secure"
        self.assertEqual(classify_control(secure, 0, 0x200)[0], "passed")
        for output in (secure.replace("0x200", "0x201"), secure + "\nExploration is incomplete",
                       "unsupported instruction", "Program status is : unknown", "Killed"):
            self.assertEqual(classify_control(output, 0, 0x200)[0], "blocked")
