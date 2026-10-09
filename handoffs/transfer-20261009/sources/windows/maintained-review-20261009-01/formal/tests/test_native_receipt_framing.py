import tempfile
import unittest
from pathlib import Path
from integration import native_receipt_framing as framing


class NativeReceiptFramingTests(unittest.TestCase):
    def test_both_real_platform_zero_framings(self):
        self.assertTrue(framing.success(b'0\n'))
        self.assertTrue(framing.success(b'0\r\n'))

    def test_nonzero_and_malformed_never_count_as_success(self):
        for data in [b'',b'0',b'0\r',b'1\n',b'98\r\n',b' 0\n',b'0 \n',
                     b'0\n\n',b'0\r\r\n',b'\xef\xbb\xbf0\r\n',b'false\n',None,0]:
            with self.subTest(data=data), self.assertRaises(ValueError):
                framing.success(data)

    def test_saved_cross_platform_receipts_and_missing_refusal(self):
        with tempfile.TemporaryDirectory() as folder:
            root=Path(folder); linux=root/'exit.txt'; windows=root/'wrapper-exit.txt'
            linux.write_bytes(b'0\n'); windows.write_bytes(b'0\r\n')
            framing.verify([linux,windows])
            windows.write_bytes(b'0\r\nextra')
            with self.assertRaises(ValueError):framing.verify([linux,windows])
            with self.assertRaises(ValueError):framing.verify([root/'unrun.txt'])
            with self.assertRaises(ValueError):framing.verify([])


if __name__=='__main__':unittest.main()
