"""Strict streaming Transfer-row decoder and contracted relation digest framing.

This validates serialized identity/shape, not row semantics or production keys.
The BLAKE3 implementation is a dependency; no cryptographic property is proved.
"""
import hashlib
import json
import re
import struct

MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513
NAMESPACE = b'_COMMONWARE_CRYPTOGRAPHY_ZK_PARI_RELATION_DIGEST'


class RelationError(ValueError):
    pass


def natural(value, bound=2**64):
    if type(value) is not int or not 0 <= value < bound:
        raise RelationError('noncanonical unsigned integer')
    return value


def record(line):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise RelationError('duplicate JSON key')
            result[key] = value
        return result
    if not line.endswith(b'\n') or not line.strip():
        raise RelationError('truncated or empty row framing')
    try:
        value = json.loads(line, object_pairs_hook=unique)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise RelationError('invalid JSON row framing') from error
    if not isinstance(value, dict):
        raise RelationError('record must be a JSON object')
    return value


def u64(value):
    return struct.pack('>Q', natural(value))


def indices(values):
    if not isinstance(values, list):
        raise RelationError('source selections must be a list')
    result = u64(len(values))
    seen = set()
    for index in values:
        if not isinstance(index, list) or len(index) != 2:
            raise RelationError('malformed source selection')
        tag, column = natural(index[0], 3), natural(index[1], 2**32)
        if (tag, column) in seen:
            raise RelationError('duplicate source selection')
        seen.add((tag, column))
        result += bytes([tag]) + struct.pack('>I', column)
    return result


def terms(values, domain):
    if not isinstance(values, list):
        raise RelationError('row terms must be a list')
    result, previous = u64(len(values)), -1
    for term in values:
        if not isinstance(term, list) or len(term) != 2:
            raise RelationError('malformed row term')
        column, encoded = natural(term[0], 2**32), term[1]
        if not previous < column < domain:
            raise RelationError('noncanonical row column order/range')
        if not isinstance(encoded, str) or not re.fullmatch('[0-9a-f]{64}', encoded):
            raise RelationError('noncanonical coefficient encoding')
        coefficient = int(encoded, 16)
        if not 0 < coefficient < MODULUS:
            raise RelationError('zero or out-of-field coefficient')
        previous = column
        result += struct.pack('>I', column) + bytes.fromhex(encoded)
    return result


def inspect(stream, expected_relation=None, row_observer=None):
    """Consume every byte, preserving row/term order and explicit EOF.

Only the exact digest may be compared to a selected key in a later qualified
join. This function has no authority to select/approve such a key.
"""
    try:
        from blake3 import blake3
    except ImportError as error:
        raise RelationError('BLAKE3 dependency unavailable; relation digest not checked') from error
    hasher, raw = blake3(), hashlib.sha256()
    first = stream.readline()
    raw.update(first)
    header = record(first)
    required = {'schema', 'family', 'relation_digest', 'domain_size', 'stored_rows', 'public_inputs',
                'committed_blocks', 'constant_column', 'public_columns', 'committed_columns',
                'source_public', 'source_blocks', 'coefficient_encoding', 'field_modulus',
                'role_provenance', 'padding'}
    if set(header) != required or header['schema'] != 'shieldd-transfer-relation-v1' or header['family'] != 'transfer':
        raise RelationError('unknown Transfer header schema')
    domain, count = natural(header['domain_size']), natural(header['stored_rows'])
    if domain < 4 or domain & (domain - 1) or count > domain:
        raise RelationError('invalid row/domain bounds')
    def column_list(values):
        if not isinstance(values, list):
            raise RelationError('column roles must be lists')
        return [natural(value, 2**32) for value in values]
    blocksizes = column_list(header['committed_blocks'])
    public_columns = column_list(header['public_columns'])
    if not isinstance(header['committed_columns'], list):
        raise RelationError('committed column roles must be blocks')
    committed_columns = [column_list(block) for block in header['committed_columns']]
    if (natural(header['public_inputs']) != 1 or blocksizes != [1]
            or natural(header['constant_column']) != 0 or public_columns != [1]
            or committed_columns != [[2]]):
        raise RelationError('wrong constant/public/committed role layout')
    if (header['coefficient_encoding'] != 'canonical-big-endian-32'
            or header['field_modulus'] != str(MODULUS)
            or header['padding'] != 'implicit-all-zero-rows-to-domain-size'
            or header['role_provenance'] != 'constant0/public prefix and committed_start=1+public_count in exact compiler'):
        raise RelationError('unknown field/encoding/padding contract')
    public, blocks = header['source_public'], header['source_blocks']
    if (not isinstance(public, list) or len(public) != 1 or not isinstance(blocks, list)
            or len(blocks) != 1 or not isinstance(blocks[0], list) or len(blocks[0]) != 1):
        raise RelationError('wrong source layout arity')
    pub_bytes, block_bytes = indices(public), indices(blocks[0])
    if public[0] == blocks[0][0] or blocks[0][0][0] == 0:
        raise RelationError('source role overlap or committed constant')
    declared = header['relation_digest']
    if not isinstance(declared, str) or not re.fullmatch('[0-9a-f]{64}', declared):
        raise RelationError('noncanonical relation digest')
    hasher.update(NAMESPACE + u64(domain) + u64(count) + pub_bytes + u64(1) + block_bytes)
    for i in range(count):
        line = stream.readline()
        raw.update(line)
        row = record(line)
        if set(row) != {'row', 'a', 'b'} or natural(row['row']) != i:
            raise RelationError('missing, reordered or unknown row')
        hasher.update(b'A' + terms(row['a'], domain) + b'B' + terms(row['b'], domain))
        if row_observer is not None:
            row_observer(row)
    line = stream.readline()
    raw.update(line)
    eof = record(line)
    if set(eof) != {'eof', 'rows'} or eof['eof'] is not True or natural(eof['rows']) != count:
        raise RelationError('missing or mismatched EOF')
    if stream.read(1):
        raise RelationError('trailing data after EOF')
    digest = hasher.hexdigest()
    if digest != declared or (expected_relation is not None and digest != expected_relation):
        raise RelationError('exported rows do not match relation digest')
    return {'schema': header['schema'], 'domain_size': domain, 'stored_rows': count,
            'relation_digest': digest, 'raw_sha256': raw.hexdigest(),
            'source_public': header['source_public'], 'source_blocks': header['source_blocks'],
            'scope': 'serialized relation identity and shape only; semantic/key/source joins open'}
