"""Read exact reviewed historical configuration/history bytes without restoring files.

Root audit helper only: sources, objects, receipts and live configs have no
fallback. Missing files outside the immutable archived phase metadata map are errors.
"""
from pathlib import Path
import hashlib, json, lzma

MAP = Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-history-metadata-preservation126-28/archive-map01.json')
MAP_SHA = '8807bbd8d63d13a5d6e3085cee3b0707c0e3b96b8ccbcf8b06c41571eee5a92a'
_table = None

def _records():
    global _table
    if _table is None:
        assert MAP.is_file() and not MAP.is_symlink()
        raw = MAP.read_bytes()
        assert len(raw) == 268296 and hashlib.sha256(raw).hexdigest() == MAP_SHA
        def unique(pairs):
            result = {}
            for key, value in pairs:
                assert key not in result
                result[key] = value
            return result
        m = json.loads(raw, object_pairs_hook=unique)
        assert m['schema'] == 'exact-inactive-phase-metadata-storage02'
        _table = m['records']
    return _table

def read_config(path, expected=None):
    p = Path(path)
    if p.exists():
        assert p.is_file() and not p.is_symlink()
        data = p.read_bytes()
    else:
        record = _records()[str(p)]
        original = record['original']
        assert original['path'] == str(p)
        assert 0 < original['bytes'] <= 16 * 1024 * 1024
        if expected is not None:
            assert original == expected
        archive = record['archive']
        q = Path(archive['path'])
        assert q.is_file() and not q.is_symlink()
        assert q.stat().st_size == archive['bytes'] <= 16 * 1024 * 1024
        packed = q.read_bytes()
        assert hashlib.sha256(packed).hexdigest() == archive['sha256']
        decoder = lzma.LZMADecompressor(memlimit=128 * 1024 * 1024)
        data = decoder.decompress(packed, max_length=original['bytes'] + 1)
        assert decoder.eof and not decoder.unused_data
        assert len(data) == original['bytes'] and hashlib.sha256(data).hexdigest() == original['sha256']
    if expected is not None:
        assert expected['path'] == str(p)
        assert len(data) == expected['bytes'] and hashlib.sha256(data).hexdigest() == expected['sha256']
    return data
