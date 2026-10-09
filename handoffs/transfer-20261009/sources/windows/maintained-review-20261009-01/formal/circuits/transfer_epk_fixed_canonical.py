"""Six EPK canonical chains inferred during the one original-row replay.

The byte tap preserves the ordinary decoder's complete stream and EOF check.
It retains bounded candidates only; unique physical comparator pairs provide
the derivative certificates. No post-canonical observer endpoint is invented.
"""
from . import transfer_relation as relation, transfer_arithmetic as arithmetic
from . import transfer_epk_fixed as epk, transfer_epk_fixed_batch as batch
from . import transfer_recovery_canonical as comparator
from .transfer_balance_rows import canonical, source_index

MAX_ROWS = 65536
MAX_TERMS = 524288
SCHEMA = 'shieldd-transfer-epk-canonical-row-derivative-v1'


def _boundaries(checked):
    boundaries = []
    occupied = set()
    for ordinal, scope in enumerate(checked['scopes']):
        page = scope['chunks'][0]; metadata = page['metadata']
        bits = [page['expressions'][source_index(bit)] for bit in metadata['bits']]
        value = page['expressions'][source_index(metadata['randomizer']['source'])]
        if (len(bits) != 252 or any(len(lc) != 1 or lc[0][1] != 1 for lc in bits)
                or len(value) != 1 or value[0][1] != 1):
            raise relation.RelationError('EPK canonical exact252 singleton bit/scalar LCs')
        columns = [lc[0][0] for lc in bits]
        private = set(columns) | {value[0][0]}
        if len(private) != 253 or occupied & private:
            raise relation.RelationError('EPK canonical six disjoint scalar/bit roles')
        occupied.update(private)
        boundaries.append(dict(checked=page, columns=columns, value=value[0][0],
            weighted=canonical((column, pow(2, index, relation.MODULUS))
                               for index, column in enumerate(columns)), scope_id=ordinal))
    if len(boundaries) != 6:
        raise relation.RelationError('EPK canonical exact six source boundaries')
    return boundaries


class _CandidateStream:
    """Forward unchanged bytes; success is granted only by relation.inspect.

    The existing arithmetic matcher owns the read lifecycle. This adapter
    never seeks, repeats, fabricates a record, or modifies qualification flags.
    """
    def __init__(self, stream, boundaries, copy):
        self.stream = stream; self.copy = copy
        self.columns = {column for selected in boundaries for column in selected['columns']}
        self.raw = {}; self.normalized = {}; self.records = {}
        self.terms = 0; self.eof = False; self.tail_checked = False

    def readline(self):
        if self.eof or self.tail_checked:
            raise relation.RelationError('EPK canonical stream read after EOF')
        line = self.stream.readline()
        record = relation.record(line)
        if set(record) == {'eof', 'rows'}:
            self.eof = True
        elif set(record) == {'row', 'a', 'b'}:
            index = relation.natural(record['row'], 200770)
            for key in ('a', 'b'): relation.terms(record[key], 262144)
            a, b = (tuple((column, int(value, 16)) for column, value in record[key])
                    for key in ('a', 'b'))
            if any(column in self.columns for column, _ in a) or not b and len(a) <= 3:
                self.terms += len(a) + len(b)
                if (index in self.records or len(self.records) >= MAX_ROWS or self.terms > MAX_TERMS):
                    raise relation.RelationError('EPK canonical bounded candidate inventory/order')
                self.records[index] = record; self.raw[index] = (a, b)
                self.normalized[index] = tuple(canonical((0 if column == self.copy else column, value)
                    for column, value in lc) for lc in (a, b))
        return line

    def read(self, size):
        if size != 1 or not self.eof or self.tail_checked:
            raise relation.RelationError('EPK canonical exact EOF tail lifecycle')
        self.tail_checked = True
        return self.stream.read(size)


def _derive(checked, boundaries, identity, raw, normalized, records):
    if (identity.get('relation_digest') != checked['parent']['relation_digest']
            or identity.get('domain_size') != 262144 or identity.get('stored_rows') != 200770):
        raise relation.RelationError('EPK canonical full ordinary identity/shape')
    scopes = []; used_all = set()
    for selected in boundaries:
        certificate, used = comparator._chain(selected, raw, normalized)
        certificate.update(scope_id=selected['scope_id'], identity=identity,
            metadata_sha256=selected['checked']['metadata_sha256'],
            selected_rows=[records[index] for index in sorted(used)])
        scopes.append(certificate); used_all.update(used)
    return dict(schema=SCHEMA, parent_sha256=checked['parent_sha256'],
        raw_page_sha256=checked['raw_page_sha256'], identity=identity, scopes=scopes,
        candidate_rows=len(records), candidate_terms=sum(len(a)+len(b) for a,b in raw.values()),
        selected_rows=len(used_all), ordinary_replays=1,
        scope='Six unique original ORDER-1 chains; native scalar seeds/nonzero/fixed-loop/full frame remain separate')


def extract_rows(qualified_parent, raw_pages, accepted_capsules, accepted_roles, stream):
    """Root-only: fixed-loop and six canonical selection, one complete replay."""
    checked = epk.inspect_all_pages(qualified_parent, raw_pages, accepted_capsules, accepted_roles)
    boundaries = _boundaries(checked)
    tap = _CandidateStream(stream, boundaries, checked['parent']['constant_copy'])
    required, products, squares, prefixes = batch._requirements(checked)
    obj = checked['parent']
    combined = arithmetic.extract_templates(tap, obj['relation_digest'], obj['domain_size'], obj['full_rows'],
        required, products, squares, label='epk-all-fixed-and-canonical')
    if not tap.eof or not tap.tail_checked:
        raise relation.RelationError('EPK canonical incomplete full replay lifecycle')
    return dict(fixed=batch._partition(checked, combined, prefixes),
        canonical=_derive(checked, boundaries, combined['identity'], tap.raw, tap.normalized, tap.records))


def _selection(checked, extracted, scope_id):
    scope_id = relation.natural(scope_id, 6)
    boundaries = _boundaries(checked)
    if (not isinstance(extracted, dict) or extracted.get('schema') != SCHEMA
            or extracted.get('parent_sha256') != checked['parent_sha256']
            or extracted.get('raw_page_sha256') != checked['raw_page_sha256']
            or type(extracted.get('ordinary_replays')) is not int or extracted['ordinary_replays'] != 1
            or not isinstance(extracted.get('scopes'), list) or len(extracted['scopes']) != 6):
        raise relation.RelationError('EPK canonical persisted parent/page/replay identity')
    selected = boundaries[scope_id]; certificate = extracted['scopes'][scope_id]
    if not isinstance(certificate, dict) or type(certificate.get('scope_id')) is not int or certificate['scope_id'] != scope_id:
        raise relation.RelationError('EPK canonical persisted scope order')
    raw, normalized = arithmetic.normalize_selection(certificate, selected['checked']['metadata'],
        selected['checked']['metadata_sha256'])
    expected, used = comparator._chain(selected, raw, normalized)
    if (set(raw) != used or comparator._json_value(extracted.get('identity')) != comparator._json_value(certificate['identity'])
            or any(comparator._json_value(certificate.get(key)) != comparator._json_value(value)
                   for key, value in expected.items())):
        raise relation.RelationError('EPK canonical original derivative certificate changed')
    return selected, certificate, expected, raw, normalized


def generate(qualified_parent, raw_pages, accepted_capsules, accepted_roles, extracted, scope_id):
    """Reaccept persisted original-row derivative before rendering one proof."""
    checked = epk.inspect_all_pages(qualified_parent, raw_pages, accepted_capsules, accepted_roles)
    selected, certificate, expected, _, _ = _selection(checked, extracted, scope_id)
    metadata = dict(constant_copy=selected['checked']['metadata']['constant_copy'],
        value=((selected['value'], 1),), steps=[])
    for step in expected['steps']:
        metadata['steps'].append([step['before'], step['left'], {'native': f"{step['right']:064x}"},
            step['factor'], step['product'], step['after']])
    source, _ = comparator.generate_linear_checked(metadata, certificate)
    return source.replace('RuntimeTransferRemainder', f'RuntimeTransferEpk{scope_id}Canonical').replace(
        'actual_remainder_canonical', 'actual_epk_randomizer_canonical')


def construction_plan(qualified_parent, raw_pages, accepted_capsules, accepted_roles, extracted):
    """Exact original product writes for native-seeded canonical construction.

    This is finite data for ScalarComparatorCompletion/CompilerCompletion,
    not an assumed endpoint, a generated proof, or surrounding-row truth.
    """
    checked = epk.inspect_all_pages(qualified_parent, raw_pages, accepted_capsules, accepted_roles)
    protected = {0, 1, 2, checked['parent']['constant_copy']}
    for scope in checked['scopes']:
        page = scope['chunks'][0]; metadata = page['metadata']
        for ref in [metadata['randomizer'], metadata['inverse'], *metadata['published'], *metadata['output']]:
            if 'source' in ref:
                protected.update(column for column, _ in page['expressions'][source_index(ref['source'])])
    all_bits = {column for selected in _boundaries(checked) for column in selected['columns']}
    if protected & all_bits:
        raise relation.RelationError('EPK canonical bit writes alias protected scalar/point/public roles')
    owned = set(all_bits); prior_support = protected | all_bits; scopes = []
    for scope_id in range(6):
        selected, certificate, expected, raw, normalized = _selection(checked, extracted, scope_id)
        columns = selected['columns']; start = columns[0]
        if columns != list(range(start, start+252)):
            raise relation.RelationError('EPK canonical constructor exact contiguous252 writes')
        products = {item['step']: item['rows'] for item in expected['products']}
        stages = []; row_sets = set()
        for index, step in enumerate(expected['steps']):
            if not index: continue
            product = arithmetic.product_certificate(step['before'], step['factor'], step['product'], normalized)
            stage = arithmetic.product_completion_certificate(step['before'], step['factor'], step['product'], product, normalized)
            if stage is None or product['rows'] != products[index]:
                raise relation.RelationError('EPK canonical actual two-write product constructor')
            writes = {stage['output'], stage['auxiliary']}
            if writes & (owned | prior_support) or row_sets & set(stage['rows']):
                raise relation.RelationError('EPK canonical product ownership/freshness')
            owned.update(writes); row_sets.update(stage['rows'])
            prior_support.update(c for row in stage['rows'] for lc in raw[row] for c, _ in lc)
            stages.append(dict(kind='product', **stage))
        templates = {item['roles'][0]: item['row'] for item in expected['templates']}
        initial = [templates['boolean'+str(i)] for i in range(252)] + [templates['reconstruction']]
        boundary = [templates['constant-copy'], templates['endpoint']]
        if set(raw) != set(initial+boundary) | row_sets:
            raise relation.RelationError('EPK canonical constructor exact original row coverage')
        scopes.append(dict(scope_id=scope_id, value=selected['value'], start=start, width=252,
            bits=columns, stages=stages, initial_rows=initial, boundary_rows=boundary,
            endpoint=expected['steps'][-1]['after'], original_rows=sorted(raw)))
    return dict(parent_sha256=checked['parent_sha256'], raw_page_sha256=checked['raw_page_sha256'],
        identity=extracted['identity'], scopes=scopes, writes=sorted(owned), protected=sorted(protected),
        capacity=2**252 < relation.MODULUS, limit=comparator.ORDER-1,
        native_seed_contract='Same admitted SDK Fr scalar n:0<n<ORDER; seed scalar LC=(n:F),constant/copy=1. No desired point/inverse/endpoint premise.',
        universal_frame='writeBits followed by exact product stages agrees with its native seed at every column outside writes; LC/row support outside transports symbolically.',
        scope='Exact canonical construction inputs only; finite checker/kernel/original transport and full six-loop composition OPEN')
