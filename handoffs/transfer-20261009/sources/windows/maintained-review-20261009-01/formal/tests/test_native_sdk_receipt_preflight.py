import tempfile
import unittest
from pathlib import Path
from integration import native_sdk_receipt_preflight as preflight


class SdkReceiptAdoptionTests(unittest.TestCase):
    def fixture(self, root, framing):
        for job in preflight.BASE:
            target=root/job;target.mkdir()
            for name in ('exit.txt','wrapper-exit.txt'):(target/name).write_bytes(framing)
            (target/'end.txt').write_bytes(b'2026-10-05\n')
            for left,right in [('sdk-source-before.txt','sdk-source-after.txt'),
                               ('formal-exporters-before.txt','formal-exporters-after.txt'),
                               ('source-inputs.txt','source-inputs-after.txt'),
                               ('runner-script-before.txt','runner-script-after.txt')]:
                (target/left).write_bytes(b'exact retained identity\n');(target/right).write_bytes(b'exact retained identity\n')
        binary=(preflight.BINARY+'  '+preflight.BINARY_PATH+'\n').encode()
        for job in preflight.BASE[4:]:
            for name in ('executed-before.txt','executed-after.txt'):(root/job/name).write_bytes(binary)
        (root/preflight.BASE[3]/'frozen-binary.sha256').write_bytes(binary)
        for job,count in zip(preflight.BASE[:3],(7,3,4)):
            (root/job/'stdout.txt').write_text(f'test result: ok. {count} passed; 0 failed;\n')

    def test_exact_lf_and_crlf_success_and_malformed_status_refusal(self):
        for framing in (b'0\n',b'0\r\n'):
            with tempfile.TemporaryDirectory() as temporary:
                root=Path(temporary);self.fixture(root,framing);preflight.verify(root)
                for bad in (b'1\n',b'0',b' 0\n',b'0\r',b'0\n0\n'):
                    (root/preflight.BASE[0]/'wrapper-exit.txt').write_bytes(bad)
                    with self.assertRaises(ValueError):preflight.verify(root)

    def test_true_zero_status_cannot_adopt_changed_source_or_wrong_unit_count(self):
        with tempfile.TemporaryDirectory() as temporary:
            root=Path(temporary);self.fixture(root,b'0\r\n')
            target=root/preflight.BASE[2]
            (target/'stdout.txt').write_text('test result: ok. 7 passed; 0 failed;\n')
            with self.assertRaisesRegex(ValueError,'unit count'):preflight.verify(root)
            (target/'stdout.txt').write_text('test result: ok. 4 passed; 0 failed;\n')
            (target/'sdk-source-after.txt').write_bytes(b'changed\n')
            with self.assertRaisesRegex(ValueError,'source changed'):preflight.verify(root)
