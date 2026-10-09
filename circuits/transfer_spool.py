"""Bounded binary RowSpool adapter; framing/data only, no semantic proof."""
import hashlib
import json
import re
import struct

from .transfer_relation import MODULUS, RelationError, indices, natural

MAX_DOMAIN = 2**22
MAX_TERMS = 32768
MAX_RECORD_BYTES = 16 * 1024 * 1024
SHAPE_KEYS = {'schema', 'domain_size', 'relation_digest', 'full_rows', 'public_inputs',
              'blocks', 'source_public', 'source_blocks', 'compilation'}


def validated_shape(shape):
    if type(shape) is not dict or set(shape) != SHAPE_KEYS:
        raise RelationError('exact spool shape keys required')
    if shape['schema'] != 'shieldd-transfer-ordered-spool-v1' or shape['compilation'] not in (
            'ordinary', 'full-program-ordinary-compiler'):
        raise RelationError('unknown spool schema/compilation')
    domain = natural(shape['domain_size'], MAX_DOMAIN + 1)
    count = natural(shape['full_rows'], 2**23)
    if domain < 4 or domain & (domain - 1) or count > domain:
        raise RelationError('invalid spool row/domain bounds')
    if type(shape['public_inputs']) is not int or shape['public_inputs'] != 1 \
            or shape['blocks'] != [1] or any(type(x) is not int for x in shape['blocks']):
        raise RelationError('wrong spool public/committed roles')
    public, blocks = shape['source_public'], shape['source_blocks']
    if type(public) is not list or len(public) != 1 or type(blocks) is not list \
            or len(blocks) != 1 or type(blocks[0]) is not list or len(blocks[0]) != 1:
        raise RelationError('wrong spool source layout arity')
    indices(public)
    indices(blocks[0])
    if public[0] == blocks[0][0] or blocks[0][0][0] == 0:
        raise RelationError('source role overlap or committed constant')
    if type(shape['relation_digest']) is not str or not re.fullmatch(
            '[0-9a-f]{64}', shape['relation_digest']):
        raise RelationError('noncanonical spool relation digest')
    # Snapshot caller data so later mutation cannot change the stream contract.
    return json.loads(json.dumps(shape))


def load_shape(stream):
    raw = stream.read(65537)
    if len(raw) > 65536:
        raise RelationError('bounded spool shape required')
    def unique(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise RelationError('duplicate spool shape key')
            result[key] = value
        return result
    try:
        shape = json.loads(raw, object_pairs_hook=unique)
    except (ValueError, UnicodeError) as error:
        raise RelationError('valid spool shape JSON required') from error
    return validated_shape(shape)


class SpoolJSONL:
    """One bounded record at a time; explicit EOF requires exact spool exhaustion.

    The unchanged relation reader recomputes BLAKE3 from decoded row bodies.
    The binary SHA separately identifies the original capture. Failure/partial
    consumption never returns a completed comparison or adapter receipt.
    """
    def __init__(self, stream, shape, observer=None):
        self.stream = stream
        self.shape = validated_shape(shape)
        self.observer = observer
        self.ordinal = -1
        self.finished = False
        self.raw = hashlib.sha256()
        self.bytes = 0

    def _exact(self, count):
        raw = self.stream.read(count)
        if type(raw) is not bytes or len(raw) != count:
            raise RelationError('truncated binary spool')
        self.raw.update(raw)
        self.bytes += len(raw)
        return raw

    def _terms(self):
        count = struct.unpack('>Q', self._exact(8))[0]
        if count > min(MAX_TERMS, self.shape['domain_size']):
            raise RelationError('finite spool term count exceeded')
        terms, previous = [], -1
        for _ in range(count):
            raw = self._exact(36)
            column = struct.unpack('>I', raw[:4])[0]
            if not previous < column < self.shape['domain_size']:
                raise RelationError('noncanonical spool column order/range')
            coefficient = int.from_bytes(raw[4:], 'big')
            if not 0 < coefficient < MODULUS:
                raise RelationError('zero or out-of-field spool coefficient')
            terms.append([column, raw[4:].hex()])
            previous = column
        return terms

    def readline(self, limit=-1):
        if self.finished:
            return b''
        shape = self.shape
        if self.ordinal == -1:
            item = dict(schema='shieldd-transfer-relation-v1', family='transfer',
                relation_digest=shape['relation_digest'], domain_size=shape['domain_size'],
                stored_rows=shape['full_rows'], public_inputs=1, committed_blocks=[1],
                constant_column=0, public_columns=[1], committed_columns=[[2]],
                source_public=shape['source_public'], source_blocks=shape['source_blocks'],
                coefficient_encoding='canonical-big-endian-32', field_modulus=str(MODULUS),
                role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',
                padding='implicit-all-zero-rows-to-domain-size')
        elif self.ordinal < shape['full_rows']:
            item = dict(row=self.ordinal, a=self._terms(), b=self._terms())
            if self.observer is not None:
                self.observer(json.loads(json.dumps(item)))
        else:
            if self.stream.read(1):
                raise RelationError('trailing binary spool data')
            item = dict(eof=True, rows=shape['full_rows'])
            self.finished = True
        self.ordinal += 1
        raw = (json.dumps(item, separators=(',', ':')) + '\n').encode()
        if len(raw) > MAX_RECORD_BYTES or (limit >= 0 and len(raw) > limit):
            raise RelationError('bounded adapter JSON record required')
        return raw

    def read(self, count):
        if count != 1 or not self.finished:
            raise RelationError('adapter must consume every row and explicit EOF')
        return b''

    def receipt(self):
        if not self.finished:
            raise RelationError('incomplete spool adapter')
        return dict(binary_sha256=self.raw.hexdigest(), binary_bytes=self.bytes,
                    rows=self.shape['full_rows'], framing='u64BE count/u32BE column/32-byte scalar',
                    completed=True, kernel_run=False, proof_credit=0)
