"""Bounded structural reader for complete Transfer arithmetic source programs.

This helper validates a complete ordered DAG, not witness values or assertion
truth. Hashes identify the stream. Neither them nor this Python check supplies
owned source meaning, a kernel graph certificate or full-row correspondence.
"""
import hashlib
import json
import re
from copy import deepcopy

FIELD_MODULUS = 52435875175126190479447740508185965837690552500527637822603658699938581184513
HEADER_KEYS = {'schema', 'family', 'witnesses', 'constants', 'nodes', 'assertions',
               'field_modulus', 'coefficient_encoding', 'source_public', 'source_blocks'}
MAX_RECORD_BYTES = 65536


class ProgramError(ValueError):
    pass


def inspect_stream(handle, consume=None):
    """Read each record once; a consumer can spool a lowering certificate.

    No list of the complete program or captured witness values is retained.
    The callback must not interpret structural success as semantic qualification.
    """
    digest = hashlib.sha256()
    records = 0

    def unique(pairs):
        value = {}
        for key, item in pairs:
            if key in value:
                raise ProgramError('duplicate program record key')
            value[key] = item
        return value

    def read():
        nonlocal records
        raw = handle.readline(MAX_RECORD_BYTES+1)
        if not raw or not isinstance(raw, bytes) or len(raw) > MAX_RECORD_BYTES:
            raise ProgramError('complete bounded binary JSONL record required')
        digest.update(raw)
        records += 1
        try:
            item = json.loads(raw, object_pairs_hook=unique)
        except (ValueError, UnicodeError) as error:
            raise ProgramError('valid UTF-8 JSON program record required') from error
        if not isinstance(item, dict):
            raise ProgramError('program record object required')
        return item

    header = read()
    if set(header) != HEADER_KEYS or header['schema'] != 'shieldd-transfer-source-program-v1' \
            or header['family'] != 'transfer' or header['field_modulus'] != str(FIELD_MODULUS) \
            or header['coefficient_encoding'] != 'canonical-big-endian-32':
        raise ProgramError('exact complete Transfer program schema required')
    for name, bound in [('witnesses', 262144), ('constants', 2**20), ('nodes', 2**22), ('assertions', 2**22)]:
        if type(header[name]) is not int or not 0 <= header[name] <= bound:
            raise ProgramError('finite exact program count required')

    def index(value, prior_nodes):
        if not isinstance(value, list) or len(value) != 2 or any(type(x) is not int for x in value):
            raise ProgramError('exact typed source index required')
        kind, ordinal = value
        bounds = {0: header['constants'], 1: header['witnesses'], 2: prior_nodes}
        if kind not in bounds or not 0 <= ordinal < bounds[kind]:
            raise ProgramError('source reference outside declared earlier program')

    if not isinstance(header['source_public'], list) or len(header['source_public']) != 1 \
            or not isinstance(header['source_blocks'], list) or len(header['source_blocks']) != 1 \
            or not isinstance(header['source_blocks'][0], list) or len(header['source_blocks'][0]) != 1:
        raise ProgramError('one public field and one committed field block required')
    index(header['source_public'][0], header['nodes'])
    index(header['source_blocks'][0][0], header['nodes'])
    if header['source_public'][0] == header['source_blocks'][0][0]:
        raise ProgramError('distinct public and committed source roles required')
    if consume is not None:
        consume(deepcopy(header))
    for ordinal in range(header['constants']):
        item = read()
        if set(item) != {'constant', 'value'} or type(item['constant']) is not int \
                or item['constant'] != ordinal or not isinstance(item['value'], str) \
                or re.fullmatch('[0-9a-f]{64}', item['value']) is None \
                or int(item['value'], 16) >= FIELD_MODULUS:
            raise ProgramError('complete ordered canonical source constants required')
        if consume is not None:
            consume(deepcopy(item))
    for ordinal in range(header['nodes']):
        item = read()
        if set(item) != {'node', 'operation', 'left', 'right'} or type(item['node']) is not int \
                or item['node'] != ordinal or item['operation'] not in ('add', 'mul'):
            raise ProgramError('complete ordered arithmetic source nodes required')
        index(item['left'], ordinal)
        index(item['right'], ordinal)
        if consume is not None:
            consume(deepcopy(item))
    for ordinal in range(header['assertions']):
        item = read()
        if set(item) != {'assertion', 'left', 'right'} or type(item['assertion']) is not int \
                or item['assertion'] != ordinal:
            raise ProgramError('complete ordered source assertions required')
        index(item['left'], header['nodes'])
        index(item['right'], header['nodes'])
        if consume is not None:
            consume(deepcopy(item))
    ending = read()
    if ending != {'end': True, 'constants': header['constants'], 'nodes': header['nodes'],
                  'assertions': header['assertions']} or type(ending.get('end')) is not bool \
            or any(type(ending.get(k)) is not int for k in ['constants', 'nodes', 'assertions']):
        raise ProgramError('exact complete source-program end record required')
    if handle.read(1):
        raise ProgramError('unexpected trailing program data')
    return {'schema': header['schema'], 'counts': {k: header[k] for k in
            ['witnesses', 'constants', 'nodes', 'assertions']}, 'records': records,
            'source_public': header['source_public'], 'source_blocks': header['source_blocks'],
            'raw_sha256': digest.hexdigest(), 'structural_reader': 'PASS',
            'source_algorithm_meaning': 'UNPROVED', 'kernel_run': False,
            'full_row_correspondence': False, 'proof_or_semantic_control_credit': 0}
