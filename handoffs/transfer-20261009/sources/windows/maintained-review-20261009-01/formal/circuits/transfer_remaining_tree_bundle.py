"""One original replay for a genuine compliance level/position/membership.

Existing strict obligations, matchers, certificates and proof renderers own
each component. The union shares only real row indices; no caller result or
row truth is supplied as a serialized acceptance flag.
"""
from . import transfer_remaining_pages as pages, transfer_arithmetic as arithmetic
from . import transfer_relation as relation

SCHEMA='shieldd-transfer-remaining-tree-bundle-v1'
KINDS=('level','position','membership')


def _requirements(manifest_data,page_data,accepted_roles,level):
    if type(level) is not int or level!=0:
        raise relation.RelationError('initial actual compliance tree level0 only')
    selected=[pages.tree_level_obligations(manifest_data,page_data,level,accepted_roles),
              pages.tree_position_obligations(manifest_data,page_data,accepted_roles),
              pages.membership_obligations(manifest_data,page_data,accepted_roles)]
    obj=selected[0]['checked']['metadata']
    if obj['scope'] not in ('sender','receiver'):
        raise relation.RelationError('compliance bundle scope')
    for item in selected:
        if item['checked']['metadata_sha256']!=selected[0]['checked']['metadata_sha256']:
            raise relation.RelationError('same exact source role page required')
    requirements=[function(item) for function,item in zip(
        (pages._tree_level_requirements,pages._tree_position_requirements,pages._membership_requirements),selected)]
    return selected,requirements


def extract(manifest_data,page_data,stream,accepted_roles,level=0):
    """Exactly one full ordered ordinary decoder run for the three slices."""
    selected,requirements=_requirements(manifest_data,page_data,accepted_roles,level)
    obj=selected[0]['checked']['metadata'];required={};products=[];squares=[]
    for kind,(direct,nonlinear,squared) in zip(KINDS,requirements):
        for row,names in direct.items():
            required.setdefault(row,[]).extend(kind+'.'+name for name in names)
        products.extend((kind+'.'+name,*args) for name,*args in nonlinear)
        squares.extend((kind+'.'+name,*args) for name,*args in squared)
    combined=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],
        required,products,squares,label='remaining-compliance-tree-bundle')
    records={row['row']:row for row in combined['selected_rows']};parts={}
    for kind in KINDS:
        prefix=kind+'.';templates=[];pairs=[];used=set()
        for template in combined['templates']:
            names=[name.removeprefix(prefix) for name in template['roles'] if name.startswith(prefix)]
            if names:
                templates.append(dict(roles=names,row=template['row']));used.add(template['row'])
        for pair in combined['products']:
            if pair['role'].startswith(prefix):
                pairs.append(dict(role=pair['role'].removeprefix(prefix),rows=pair['rows']));used.update(pair['rows'])
        part=dict(identity=combined['identity'],templates=templates,products=pairs,
                  selected_rows=[records[index] for index in sorted(used)],
                  metadata_sha256=selected[0]['checked']['metadata_sha256'])
        if kind=='level':part.update(tree_level=level,tree_scope=obj['scope'])
        elif kind=='position':part.update(tree_scope=obj['scope'])
        else:part.update(membership_scope=obj['scope'])
        parts[kind]=part
    result=dict(schema=SCHEMA,scope=obj['scope'],level=level,identity=combined['identity'],parts=parts,
                selected_rows=combined['selected_rows'],metadata_sha256=selected[0]['checked']['metadata_sha256'],
                ordinary_replays=1,semantic_scope='Only local actual children,32-bit position and regulated root gate; hashes/lifecycle/native/full UserSem remain open')
    validate(manifest_data,page_data,result,accepted_roles)
    return result


def validate(manifest_data,page_data,extracted,accepted_roles):
    selected,_=_requirements(manifest_data,page_data,accepted_roles,0)
    obj=selected[0]['checked']['metadata']
    if (not isinstance(extracted,dict) or set(extracted)!={'schema','scope','level','identity','parts','selected_rows','metadata_sha256','ordinary_replays','semantic_scope'}
            or extracted['schema']!=SCHEMA or extracted['scope']!=obj['scope']
            or type(extracted['level']) is not int or extracted['level']!=0
            or type(extracted['ordinary_replays']) is not int or extracted['ordinary_replays']!=1
            or extracted['metadata_sha256']!=selected[0]['checked']['metadata_sha256']
            or not isinstance(extracted['parts'],dict) or set(extracted['parts'])!=set(KINDS)):
        raise relation.RelationError('closed same-page actual tree bundle')
    arithmetic.normalize_selection(extracted,obj,selected[0]['checked']['metadata_sha256'])
    rows={row['row']:row for row in extracted['selected_rows']};used=set()
    for kind,part in extracted['parts'].items():
        keys={'identity','templates','products','selected_rows','metadata_sha256'}|(
            {'tree_level','tree_scope'} if kind=='level' else {'tree_scope'} if kind=='position' else {'membership_scope'})
        if (not isinstance(part,dict) or set(part)!=keys or not isinstance(part['selected_rows'],list)
                or part.get('identity')!=extracted['identity'] or part.get('metadata_sha256')!=extracted['metadata_sha256']):
            raise relation.RelationError('bundle component identity mismatch')
        for row in part['selected_rows']:
            if rows.get(row['row'])!=row:raise relation.RelationError('component physical row changed')
            used.add(row['row'])
    if used!=set(rows):raise relation.RelationError('bundle exact physical-row union coverage')
    pages.tree_level_certificates(manifest_data,page_data,0,extracted['parts']['level'],accepted_roles)
    pages.tree_position_certificates(manifest_data,page_data,extracted['parts']['position'],accepted_roles)
    pages.membership_certificates(manifest_data,page_data,extracted['parts']['membership'],accepted_roles)
    return selected[0]['checked']


def generate(manifest_data,page_data,extracted,accepted_roles):
    checked=validate(manifest_data,page_data,extracted,accepted_roles)
    prefix='RuntimeTransfer'+checked['metadata']['scope'].capitalize()
    return [(prefix+'TreeLevel000',pages.generate_tree_level(manifest_data,page_data,0,extracted['parts']['level'],accepted_roles)),
            (prefix+'TreePosition',pages.generate_tree_position(manifest_data,page_data,extracted['parts']['position'],accepted_roles)),
            (prefix+'MembershipGate',pages.generate_membership(manifest_data,page_data,extracted['parts']['membership'],accepted_roles))]
