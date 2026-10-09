"""Strict native guard status framing for Linux LF and PowerShell CRLF."""
from pathlib import Path
import sys


def success(data):
    """Only an exact saved zero status counts; no trimming or coercion."""
    if type(data) is not bytes or data not in (b'0\n', b'0\r\n'):
        raise ValueError('exact zero LF/CRLF native receipt required')
    return True


def verify(paths):
    if not paths:
        raise ValueError('native receipt paths required')
    for raw in paths:
        path = Path(raw)
        if not path.is_file() or path.is_symlink():
            raise ValueError('regular actual native receipt required')
        with path.open('rb') as stream:
            success(stream.read(4))


if __name__ == '__main__':
    verify(sys.argv[1:])
