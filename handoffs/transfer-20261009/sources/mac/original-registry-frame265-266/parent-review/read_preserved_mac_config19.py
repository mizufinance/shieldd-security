"""Read exact reviewed historical configuration/history bytes without restoring files.

Root audit helper only: sources, objects, receipts and live configs have no
fallback. Missing files outside the immutable archived phase metadata map are errors.
"""
from pathlib import Path
import hashlib, json, lzma

MAP = Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-history-metadata-preservation126-43/archive-map01.json')
MAP_SHA = 'e994d6fc233c5b95dd9975d71fdfad31c632a5509b7c1a9528cb4769b8343d23'
_table = None

def _records():
    global _table
    if _table is None:
        assert MAP.is_file() and not MAP.is_symlink()
        raw = MAP.read_bytes()
        assert len(raw) == 1585505 and hashlib.sha256(raw).hexdigest() == MAP_SHA
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

def read_original(path, expected=None):
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

def read_config(path, expected=None):
    raw=read_original(path,expected)
    if expected is not None:return raw
    wrapper=json.loads(raw)
    if wrapper.get('schema')!='bounded-pinned-execution-delta01':return raw
    assert set(wrapper)=={'schema','base','replace','merge','effective_sha256','effective_bytes'}
    base=wrapper['base'];assert set(base)=={'path','bytes','sha256'}and 0<base['bytes']<=16*1024*1024
    result=json.loads(read_original(base['path'],base));assert result.get('schema')!='bounded-pinned-execution-delta01'
    assert set(wrapper['replace'])<=set(result)and set(wrapper['merge'])<=set(result)and not(set(wrapper['replace'])&set(wrapper['merge']))
    result.update(wrapper['replace'])
    for key,value in wrapper['merge'].items():
        assert key in {'static_records','modules','qualified_batch_imports'}and isinstance(result[key],dict)and isinstance(value,dict)
        result[key].update(value)
    effective=(json.dumps(result,sort_keys=True,separators=(',',':'))+'\n').encode()
    assert len(effective)==wrapper['effective_bytes']<=32*1024*1024 and hashlib.sha256(effective).hexdigest()==wrapper['effective_sha256']
    return effective
