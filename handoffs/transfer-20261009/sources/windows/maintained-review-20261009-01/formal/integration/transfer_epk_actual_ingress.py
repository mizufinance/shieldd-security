"""Actual six-EPK row replay and bounded maintained proof consumers.

Qualification comes from the native four-spool qualifier. This adapter does not
set flags, execute a compiler, or accept a serialized caller-success assertion.
One replay selects the six loops, canonical chains and original boundaries;
every later consumer reaccepts the exact parent and retained row selection.
"""
import hashlib
from circuits import transfer_relation as relation
from circuits import transfer_epk_fixed as epk, transfer_epk_fixed_rows as rows
from circuits import transfer_epk_fixed_batch as batch, transfer_epk_fixed_program as program
from circuits import transfer_epk_fixed_sequence as sequence
from circuits import generate_transfer_epk_fixed_completion as render


def _ids(parent, pages):
    return hashlib.sha256(parent).hexdigest(), [hashlib.sha256(page).hexdigest() for page in pages]


def replay(parent, pages, capsules, caller, stream):
    # Inspect all real roles before the caller opens/advances an ordinary stream.
    epk.inspect_all_pages(parent, pages, capsules, caller)
    extracted = rows.extract_rows(parent, pages, capsules, caller, stream)
    digest, page_ids = _ids(parent, pages)
    if (extracted.get('parent_sha256') != digest or extracted.get('raw_page_sha256') != page_ids
            or type(extracted.get('ordinary_replays')) is not int or extracted['ordinary_replays'] != 1):
        raise relation.RelationError('EPK one-replay retained parent identity')
    return extracted


def _selector(kind, scope, page):
    if kind not in ('canonical', 'page', 'whole', 'six'):
        raise relation.RelationError('EPK supported constructive consumer required')
    if kind == 'six':
        if scope is not None or page is not None:
            raise relation.RelationError('EPK six-loop consumer has no local selector')
    elif type(scope) is not int or not 0 <= scope < 6:
        raise relation.RelationError('EPK exact six-scope index')
    elif kind == 'page':
        if type(page) is not int or not 0 <= page < 8:
            raise relation.RelationError('EPK exact eight-page local index')
    elif page is not None:
        raise relation.RelationError('EPK nonpage consumer has no page selector')


def generate(parent, pages, capsules, caller, extracted, kind, scope=None, page=None):
    """Yield actual source only. A page emits every reachable local constructor.

    Whole-loop modules import previously emitted canonical/page modules. The six
    composition imports the six native-boundary modules. No kernel credit is
    conferred by this source renderer or its extraction-identity checks.
    """
    _selector(kind, scope, page)
    digest, page_ids = _ids(parent, pages)
    if (not isinstance(extracted, dict) or extracted.get('parent_sha256') != digest
            or extracted.get('raw_page_sha256') != page_ids
            or type(extracted.get('ordinary_replays')) is not int or extracted['ordinary_replays'] != 1):
        raise relation.RelationError('EPK retained actual replay identity required')
    if kind == 'six':
        yield 'RuntimeTransferEpkSixCompletion', sequence.generate(parent, pages, capsules, caller, extracted)
        return
    accepted = program.plan(parent, pages, capsules, caller, extracted, scope)
    if kind == 'canonical':
        yield from render.generate_canonical(parent, pages, capsules, caller, extracted['canonical'], scope).items()
        return
    if kind == 'whole':
        # Existing default full-scope renderer produces local Program adapters
        # alongside the eight chunk/full/frame/native consumers, once each.
        yield from program.generate_scope(parent, pages, capsules, caller, extracted, scope).items()
        return
    ordinal = scope * 8 + page
    checked = epk.inspect_all_pages(parent, pages, capsules, caller)
    batch.page_selection(checked, extracted['fixed'], ordinal)
    chunk = accepted['chunks'][page]
    start = chunk['metadata']['window_start']
    for offset in range(chunk['metadata']['window_count']):
        stem = f'RuntimeTransferEpk{scope}FixedWindow{start+offset:03d}'
        for suffix, renderer in (('', render.generate_window), ('Completion', render.generate_window_completion),
                                  ('CurveCompletion', render.generate_window_complete)):
            yield stem + suffix, renderer(parent, pages, capsules, caller, extracted['fixed'], scope, page, offset)

