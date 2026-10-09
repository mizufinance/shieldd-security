"""Bounded candidate iteration for actual variable-base constructors.

Callers reaccept capture metadata and retain independently replayed selections.
This module neither reads the ordinary stream nor qualifies candidate proofs.
The root can freeze its producer and generate one at-most16-window chunk per
admitted process; the symbolic whole loop consumes all126 exact adapters.
"""
from . import transfer_ownership as owner
from . import transfer_relation as relation
from . import generate_transfer_ownership_point_materializations as material
from . import generate_transfer_ownership_double_completion as double
from . import generate_transfer_ownership_add_completion as addition
from . import generate_transfer_ownership_native_seed as native_seed
from . import generate_transfer_ownership_precompute_native as native_precompute
from . import generate_transfer_ownership_folded_window_completion as folded
from . import generate_transfer_ownership_folded_window_curve as folded_curve
from . import generate_transfer_ownership_selector_completion as selector
from . import generate_transfer_ownership_window_curve_completion as whole
from . import generate_transfer_ownership_window_program as program


def _chunk(checked, extracted):
    if not isinstance(checked, dict) or not isinstance(extracted, dict):
        raise relation.RelationError('ownership constructor typed accepted chunk/selection')
    metadata = checked.get('metadata'); windows = checked.get('windows')
    if not isinstance(metadata, dict) or not isinstance(windows, list):
        raise relation.RelationError('ownership constructor accepted metadata/window list')
    start, count = metadata.get('window_start'), metadata.get('window_count')
    if type(start) is not int or type(count) is not int or not 0 <= start < 126 or \
            not 1 <= count <= 16 or start+count > 126 or len(windows) != count:
        raise relation.RelationError('ownership constructor exact bounded chunk')
    digest = metadata.get('relation_digest')
    domain, rows = relation.natural(metadata.get('domain_size')), relation.natural(metadata.get('full_rows'))
    if not isinstance(digest,str) or len(digest) != 64 or any(char not in '0123456789abcdef' for char in digest) or \
            not 0 < rows <= domain:
        raise relation.RelationError('ownership constructor canonical relation identity')
    identity = extracted.get('identity')
    if not isinstance(identity, dict) or identity.get('schema') != 'shieldd-transfer-relation-v1' or \
            identity.get('relation_digest') != digest or \
            type(identity.get('domain_size')) is not int or identity['domain_size'] != domain or \
            type(identity.get('stored_rows')) is not int or identity['stored_rows'] != rows or \
            not isinstance(extracted.get('selected_rows'), list):
        raise relation.RelationError('ownership constructor retained exact row-selection identity')
    # Identity is not a proof of extraction. Each maintained component matcher
    # below validates its actual sparse rows, operands and source certificates.
    return start, count


def validate_all_chunks(chunks, selections):
    """Strict all126 source-role, adjacency and shared-graph join before staging."""
    if not isinstance(chunks, list) or not isinstance(selections, list) or len(chunks) != len(selections):
        raise relation.RelationError('ownership constructor paired accepted chunks/selections')
    for checked, extracted in zip(chunks,selections):
        _chunk(checked,extracted)
    return owner.join_chunks(chunks)


def iter_candidates(checked, extracted, readonly_lcs=()):
    """Yield bounded maintained candidates in their dependency order.

    Initial table precomputation appears once, in the start0 chunk. The first
    native-identity window is folded; every later window owns both nonlinear
    doubles, selector materializations and nonlinear affine addition. No
    quotient legality or desired point/row truth is an input to this API.
    """
    start, count = _chunk(checked,extracted)
    names = set()
    def unique(pair):
        name, source = pair
        if name in names:
            raise relation.RelationError('ownership constructor duplicate candidate module')
        names.add(name)
        return name, source
    if start == 0:
        for pair in material.generate(checked,extracted,0,True,readonly_lcs):
            yield unique(pair)
        for renderer in (double,addition,native_seed,native_precompute):
            yield unique(renderer.generate(checked,extracted,readonly_lcs))
    for offset in range(count):
        if start+offset == 0:
            yield unique(folded.generate(checked,extracted,readonly_lcs))
            yield unique(folded_curve.generate(checked,extracted,readonly_lcs))
        else:
            for pair in material.generate(checked,extracted,offset,False,readonly_lcs):
                yield unique(pair)
            for axis in (0,1):
                yield unique(double.generate_window_double(checked,extracted,offset,axis,readonly_lcs))
            yield unique(addition.generate_window_addition(checked,extracted,offset,readonly_lcs))
            yield unique(selector.generate(checked,extracted,offset,readonly_lcs))
            yield unique(whole.generate(checked,extracted,offset,readonly_lcs))
        yield unique(program.generate(checked,extracted,offset,readonly_lcs))
