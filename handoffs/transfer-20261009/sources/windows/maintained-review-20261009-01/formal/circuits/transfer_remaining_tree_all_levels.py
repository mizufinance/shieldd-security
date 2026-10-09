"""One original-row union for all sixteen compliance levels and existing gates.

This reuses the maintained per-level/position/membership certificates and
renderers. It establishes no hash result, lifecycle predicate or native law.
"""
from . import transfer_remaining_pages as pages, transfer_arithmetic as arithmetic
from . import transfer_relation as relation

SCHEMA = 'shieldd-transfer-remaining-tree-all-levels-v1'
KINDS = tuple(f'level{i:03}' for i in range(16)) + ('position', 'membership')
SCOPE = 'Sixteen original local child wirings,32-bit position and regulated root gate only; hashes,lifecycle,native and full UserSem remain open'


def _requirements(manifest_data, page_data, accepted_roles):
    levels = [pages.tree_level_obligations(manifest_data, page_data, i, accepted_roles) for i in range(16)]
    selected = levels + [pages.tree_position_obligations(manifest_data, page_data, accepted_roles),
                         pages.membership_obligations(manifest_data, page_data, accepted_roles)]
    checked = levels[0]['checked']
    if checked['metadata']['scope'] not in ('sender', 'receiver'):
        raise relation.RelationError('exact sixteen-level compliance scope')
    if any(item['checked']['metadata_sha256'] != checked['metadata_sha256'] for item in selected):
        raise relation.RelationError('same source page throughout compliance union')
    requirements = [pages._tree_level_requirements(item) for item in levels]
    requirements += [pages._tree_position_requirements(selected[-2]), pages._membership_requirements(selected[-1])]
    return checked, requirements


def extract(manifest_data, page_data, stream, accepted_roles):
    checked, requirements = _requirements(manifest_data, page_data, accepted_roles)
    obj = checked['metadata']; required = {}; products = []; squares = []
    for kind, (direct, nonlinear, squared) in zip(KINDS, requirements):
        for row, names in direct.items():
            required.setdefault(row, []).extend(kind + '.' + name for name in names)
        products.extend((kind + '.' + name, *args) for name, *args in nonlinear)
        squares.extend((kind + '.' + name, *args) for name, *args in squared)
    combined = arithmetic.extract_templates(stream, obj['relation_digest'], obj['domain_size'], obj['full_rows'],
                                            required, products, squares, label='remaining-compliance-all-levels')
    rows = {row['row']: row for row in combined['selected_rows']}; parts = {}
    for kind in KINDS:
        prefix = kind + '.'; templates = []; pairs = []; used = set()
        for template in combined['templates']:
            names = [name.removeprefix(prefix) for name in template['roles'] if name.startswith(prefix)]
            if names:
                templates.append(dict(roles=names, row=template['row'])); used.add(template['row'])
        for pair in combined['products']:
            if pair['role'].startswith(prefix):
                pairs.append(dict(role=pair['role'].removeprefix(prefix), rows=pair['rows'])); used.update(pair['rows'])
        part = dict(identity=combined['identity'], templates=templates, products=pairs,
                    selected_rows=[rows[index] for index in sorted(used)], metadata_sha256=checked['metadata_sha256'])
        if kind.startswith('level'): part.update(tree_level=int(kind[5:]), tree_scope=obj['scope'])
        elif kind == 'position': part.update(tree_scope=obj['scope'])
        else: part.update(membership_scope=obj['scope'])
        parts[kind] = part
    result = dict(schema=SCHEMA, scope=obj['scope'], identity=combined['identity'], parts=parts,
                  selected_rows=combined['selected_rows'], metadata_sha256=checked['metadata_sha256'],
                  ordinary_replays=1, semantic_scope=SCOPE)
    validate(manifest_data, page_data, result, accepted_roles)
    return result


def validate(manifest_data, page_data, extracted, accepted_roles):
    checked, _ = _requirements(manifest_data, page_data, accepted_roles)
    obj = checked['metadata']
    if (not isinstance(extracted, dict) or set(extracted) != {'schema', 'scope', 'identity', 'parts', 'selected_rows', 'metadata_sha256', 'ordinary_replays', 'semantic_scope'}
            or extracted['schema'] != SCHEMA or extracted['scope'] != obj['scope']
            or type(extracted['ordinary_replays']) is not int or extracted['ordinary_replays'] != 1
            or extracted['semantic_scope'] != SCOPE or extracted['metadata_sha256'] != checked['metadata_sha256']
            or not isinstance(extracted['parts'], dict) or set(extracted['parts']) != set(KINDS)):
        raise relation.RelationError('closed same-page sixteen-level actual row union')
    arithmetic.normalize_selection(extracted, obj, checked['metadata_sha256'])
    rows = {row['row']: row for row in extracted['selected_rows']}; used = set()
    for kind in KINDS:
        part = extracted['parts'][kind]
        keys = {'identity', 'templates', 'products', 'selected_rows', 'metadata_sha256'} | (
            {'tree_level', 'tree_scope'} if kind.startswith('level') else {'tree_scope'} if kind == 'position' else {'membership_scope'})
        if (not isinstance(part, dict) or set(part) != keys or not isinstance(part['selected_rows'], list)
                or part['identity'] != extracted['identity'] or part['metadata_sha256'] != extracted['metadata_sha256']):
            raise relation.RelationError('all-level component identity mismatch')
        for row in part['selected_rows']:
            if not isinstance(row, dict) or rows.get(row.get('row')) != row:
                raise relation.RelationError('all-level physical row mismatch')
            used.add(row['row'])
        if kind.startswith('level'):
            pages.tree_level_certificates(manifest_data, page_data, int(kind[5:]), part, accepted_roles)
        elif kind == 'position': pages.tree_position_certificates(manifest_data, page_data, part, accepted_roles)
        else: pages.membership_certificates(manifest_data, page_data, part, accepted_roles)
    if used != set(rows): raise relation.RelationError('exact all-level physical row union coverage')
    return checked


def generate(manifest_data, page_data, extracted, accepted_roles):
    checked = validate(manifest_data, page_data, extracted, accepted_roles)
    prefix = 'RuntimeTransfer' + checked['metadata']['scope'].capitalize()
    modules = [(prefix + f'TreeLevel{i:03}', pages.generate_tree_level(manifest_data, page_data, i, extracted['parts'][f'level{i:03}'], accepted_roles)) for i in range(16)]
    return modules + [(prefix + 'TreePosition', pages.generate_tree_position(manifest_data, page_data, extracted['parts']['position'], accepted_roles)),
                      (prefix + 'MembershipGate', pages.generate_membership(manifest_data, page_data, extracted['parts']['membership'], accepted_roles))]
