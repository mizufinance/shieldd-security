"""One actual row union for a complete current compliance hash scope.

Every page retains its existing source DAG, source/LC edges and pinned tables.
This does not give an observer new continuity or prove lifecycle/native laws.
The owning root driver alone opens the original relation once.
"""
import hashlib
from . import transfer_remaining_pages as pages,transfer_note_hash as hashes
from . import transfer_arithmetic as arithmetic,transfer_relation as relation
from .transfer_balance_rows import canonical,combine,source_index

SCHEMA='shieldd-transfer-compliance-hash-union-v1'
SCOPE='Original leaf/two-block and sixteen path hash materializations only; wiring/lifecycle/native/whole UserSem composition remains separate'
MAX_ROWS=8192


def checked_pages(manifest_data,page_data,accepted_roles,parameter_root):
    """Yield one accepted cone at a time, with all actual cross-page ties."""
    manifest=pages.inspect_manifest(manifest_data,accepted_roles['metadata']['relation_digest'])
    if manifest['scope'] not in ('sender','receiver') or not isinstance(page_data,(list,tuple)) or len(page_data)!=19:
        raise relation.RelationError('exact nineteen-page current compliance hash scope')
    role=pages.inspect_page(manifest_data,page_data[0],0,accepted_roles)
    shared=dict(role['observed'])
    for ordinal in range(1,19):
        checked=pages.inspect_page(manifest_data,page_data[ordinal],ordinal,accepted_roles,parameter_root)
        if (checked['records']!=role['records'] or checked['metadata']['calls']!=role['metadata']['calls']
                or any(checked['metadata'][key]!=role['metadata'][key] for key in pages.IDENTITY)
                or checked['graph']['width']!=6):
            raise relation.RelationError('same actual compliance role/source/width across all hash pages')
        for handle,lc in checked['observed'].items():
            if handle in shared and shared[handle]!=lc:
                raise relation.RelationError('compliance hash cross-page LC changed')
            shared[handle]=lc
        yield ordinal,checked


def _requirements(checked):
    obj=checked['metadata'];copy=obj['constant_copy']
    outlined=lambda lc:canonical((copy if c==0 else c,v) for c,v in lc)
    direct={(canonical([(0,1),(copy,-1)]),()):['constant-copy']};products=[]
    for ref,(multiply,left,right) in checked['nodes'].items():
        if not multiply:continue
        a,b,z=(checked['derived'][item] for item in (left,right,ref))
        if any(all(c==0 for c,_ in lc) for lc in (a,b)):continue
        name='node.'+str(ref[1])
        if a==b:direct.setdefault((outlined(a),outlined(z)),[]).append(name)
        else:products.append((name,outlined(combine(a,b,-1)),outlined(combine(a,b)),outlined(z)))
    return direct,products


def _retain(stream,obj,required,products):
    """Strict unique physical template selection, including both orientations."""
    targets={a for _,minus,plus,_ in products for a in (minus,canonical((c,-v) for c,v in minus),plus)}
    direct={};candidates={};rows={}
    def observe(row):
        a,b=(tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b'))
        key=(a,b)
        if key in required:
            direct.setdefault(key,[]).append(row['row']);rows[row['row']]=row
        if a in targets:
            candidates.setdefault(a,[]).append((b,row['row']));rows[row['row']]=row
            if len(candidates[a])>256:raise relation.RelationError('compliance union bounded physical candidates')
    identity=relation.inspect(stream,expected_relation=obj['relation_digest'],row_observer=observe)
    if identity['stored_rows']!=obj['full_rows'] or identity['domain_size']!=obj['domain_size']:
        raise relation.RelationError('compliance union exact complete original relation shape')
    if set(direct)!=set(required) or any(len(indices)!=1 for indices in direct.values()):
        raise relation.RelationError('compliance union missing/ambiguous direct physical row')
    selected={key:indices[0] for key,indices in direct.items()};pairs=[]
    for name,minus,plus,output in products:
        found=[]
        negative=canonical((c,-v) for c,v in minus)
        left=candidates.get(minus,[])+(candidates.get(negative,[]) if negative!=minus else [])
        for auxiliary,first in left:
            wanted=combine(auxiliary,output,4)
            for total,second in candidates.get(plus,[]):
                if first<second and total==wanted:found.append((first,second))
        found=list(dict.fromkeys(found))
        if len(found)!=1:raise relation.RelationError('compliance union missing/ambiguous actual materialization: '+name)
        pairs.append(dict(role=name,rows=list(found[0])))
    used=set(selected.values())|{index for pair in pairs for index in pair['rows']}
    if not 1<=len(used)<=MAX_ROWS:raise relation.RelationError('bounded compliance union physical row inventory')
    return dict(identity=identity,templates=[dict(roles=required[key],row=index) for key,index in selected.items()],
                products=pairs,selected_rows=[rows[index] for index in sorted(used)])


def extract(manifest_data,page_data,stream,accepted_roles,parameter_root):
    requirements={};products=[];identities={};obj=None
    for ordinal,checked in checked_pages(manifest_data,page_data,accepted_roles,parameter_root):
        obj=checked['metadata'];identities[str(ordinal)]=checked['metadata_sha256']
        direct,nonlinear=_requirements(checked);prefix=str(ordinal)+'.'
        for row,names in direct.items():requirements.setdefault(row,[]).extend(prefix+name for name in names)
        products.extend((prefix+name,minus,plus,output) for name,minus,plus,output in nonlinear)
    combined=_retain(stream,obj,requirements,products)
    rows={row['row']:row for row in combined['selected_rows']};parts={}
    # Metadata is independently reaccepted without retaining all eighteen DAGs.
    for ordinal,checked in checked_pages(manifest_data,page_data,accepted_roles,parameter_root):
        prefix=str(ordinal)+'.';templates=[];nonlinear=[];used=set()
        for item in combined['templates']:
            names=[name.removeprefix(prefix) for name in item['roles'] if name.startswith(prefix)]
            if names:templates.append(dict(roles=names,row=item['row']));used.add(item['row'])
        for item in combined['products']:
            if item['role'].startswith(prefix):
                nonlinear.append(dict(role=item['role'].removeprefix(prefix),rows=item['rows']));used.update(item['rows'])
        meta=checked['metadata']
        parts[str(ordinal)]=dict(identity=combined['identity'],templates=templates,products=nonlinear,
            selected_rows=[rows[index] for index in sorted(used)],metadata_sha256=identities[str(ordinal)],
            slot=meta['slot'],role=meta['role'],level=meta['level'],block=meta['block'],scope=SCOPE)
    result=dict(schema=SCHEMA,scope=obj['scope'],identity=combined['identity'],parts=parts,
        selected_rows=combined['selected_rows'],manifest_sha256=hashlib.sha256(manifest_data).hexdigest(),
        page_sha256=[hashlib.sha256(data).hexdigest() for data in page_data],ordinary_replays=1,semantic_scope=SCOPE)
    validate(manifest_data,page_data,result,accepted_roles,parameter_root)
    return result


def validate(manifest_data,page_data,extracted,accepted_roles,parameter_root):
    if (not isinstance(extracted,dict) or set(extracted)!={'schema','scope','identity','parts','selected_rows','manifest_sha256','page_sha256','ordinary_replays','semantic_scope'}
            or extracted['schema']!=SCHEMA or extracted['semantic_scope']!=SCOPE or type(extracted['ordinary_replays']) is not int
            or extracted['ordinary_replays']!=1 or extracted['manifest_sha256']!=hashlib.sha256(manifest_data).hexdigest()
            or extracted['page_sha256']!=[hashlib.sha256(data).hexdigest() for data in page_data]
            or not isinstance(extracted['parts'],dict) or set(extracted['parts'])!={str(i) for i in range(1,19)}):
        raise relation.RelationError('closed exact nineteen-page compliance hash derivative')
    role=pages.inspect_page(manifest_data,page_data[0],0,accepted_roles)
    arithmetic.normalize_selection({**extracted,'metadata_sha256':role['metadata_sha256']},role['metadata'],role['metadata_sha256'])
    used=set();raw={row['row']:row for row in extracted['selected_rows']}
    for ordinal,checked in checked_pages(manifest_data,page_data,accepted_roles,parameter_root):
        if extracted['scope']!=checked['metadata']['scope']:raise relation.RelationError('same compliance component throughout')
        part=extracted['parts'][str(ordinal)]
        if (not isinstance(part,dict) or set(part)!={'identity','templates','products','selected_rows','metadata_sha256','slot','role','level','block','scope'}
                or part['identity']!=extracted['identity'] or part['scope']!=SCOPE):
            raise relation.RelationError('compliance hash derivative exact part shape/identity')
        # Normalization also validates ordering, canonical terms and copy link.
        arithmetic.normalize_selection(part,checked['metadata'],checked['metadata_sha256'])
        direct,products=_requirements(checked)
        expected=_match_part(part['selected_rows'],direct,products)
        if (part['templates']!=expected['templates'] or part['products']!=expected['products']
                or part['selected_rows']!=expected['selected_rows']):
            raise relation.RelationError('compliance hash exact unique physical source templates changed')
        hashes._select_permutation(checked,part,parameter_root,role_prefix='remaining')
        for row in part['selected_rows']:
            if raw.get(row['row'])!=row:raise relation.RelationError('compliance hash union physical row changed')
            used.add(row['row'])
    if not 1<=len(raw)<=MAX_ROWS or len(raw)!=len(extracted['selected_rows']) or used!=set(raw):
        raise relation.RelationError('compliance hash exact full physical union coverage')
    return extracted


def _match_part(rows,required,products):
    """Recheck all declared source templates against only their retained rows."""
    by_row={};by_a={};physical={row['row']:row for row in rows}
    for row in rows:
        a,b=(tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b'))
        by_row.setdefault((a,b),[]).append(row['row']);by_a.setdefault(a,[]).append((b,row['row']))
    templates=[];pairs=[];used=set()
    for key,names in required.items():
        indices=by_row.get(key,[])
        if len(indices)!=1:raise relation.RelationError('compliance hash retained direct template ambiguity')
        templates.append(dict(roles=names,row=indices[0]));used.add(indices[0])
    for name,minus,plus,output in products:
        negative=canonical((c,-v) for c,v in minus)
        candidates=by_a.get(minus,[])+(by_a.get(negative,[]) if negative!=minus else [])
        found=list(dict.fromkeys((first,second) for auxiliary,first in candidates
            for total,second in by_a.get(plus,[]) if first<second and total==combine(auxiliary,output,4)))
        if len(found)!=1:raise relation.RelationError('compliance hash retained product template ambiguity')
        pairs.append(dict(role=name,rows=list(found[0])));used.update(found[0])
    return dict(templates=templates,products=pairs,selected_rows=[physical[index] for index in sorted(used)])


def generate_call(manifest_data,page_data,extracted,accepted_roles,parameter_root,call_index):
    """Yield bounded sound/constructive modules for one existing source call.

    This constructs this call's hash rows from arbitrary base assignment; it
    does not assume prior tree rows or a wanted hash/root value.
    """
    from . import transfer_note_hash_join as joins,generate_note_hash_block_completion as blocks
    from . import generate_note_hash_call_completion as calls
    call_index=relation.natural(call_index,17)
    validate(manifest_data,page_data,extracted,accepted_roles,parameter_root)
    ordinals=[1,2] if call_index==0 else [call_index+2]
    checked=[];selections=[]
    for ordinal,item in checked_pages(manifest_data,page_data,accepted_roles,parameter_root):
        if ordinal in ordinals:
            checked.append(item);selections.append(hashes._select_permutation(item,extracted['parts'][str(ordinal)],parameter_root,role_prefix='remaining'))
    obj=checked[0]['metadata'];base='RuntimeTransfer'+obj['scope'].capitalize()+('LeafHash' if call_index==0 else f'TreeHash{call_index-1:03}')
    if any(part['metadata']['hash']!=obj['hash'] for part in checked) or [part['block'] for part in checked]!=list(range(len(checked))):
        raise relation.RelationError('complete compliance source call/block adjacency')
    yield from joins._generate_checked(checked,selections,base,width=6)
    readonly=list(accepted_roles['observed'].values())
    for ref in obj['hash']['inputs']:
        if 'source' in ref:readonly.append(checked[0]['observed'][source_index(ref['source'])])
    for block,(item,selected) in enumerate(zip(checked,selections)):
        prefix=base+f'Block{block}' if len(checked)==2 else base
        context=(selected,item,dict(metadata={},readonly_lcs=readonly));chunks=[];owned=set();support=set();rows=set()
        for index,start in enumerate(range(0,65,5)):
            plan=blocks._chunk_plan(context,start,min(start+5,65))
            if set(plan['writes'])&(owned|support):raise relation.RelationError('compliance hash later chunk changes earlier rows')
            owned.update(plan['writes']);support.update(c for row in plan['raw'].values() for lc in row for c,_ in lc);rows.update(plan['raw'])
            module,source=blocks._chunk_source(prefix,index,plan,chunks);yield module,source;chunks.append(module)
        if rows!=set(selected['rows']):raise relation.RelationError('compliance hash full local materialization coverage')
        permutation='RuntimeHashBlock_'+selected['calls'][0]['role'].replace('.','_')+'_0'
        yield prefix+'Completion',blocks._composition(prefix,chunks,item['metadata'],
            rows_only=len(checked)==2,sound_module=prefix+'_Composition' if len(checked)==2 else base,
            sound_namespace=permutation if len(checked)==2 else base,width=6,permutation_namespace=permutation)
    if len(checked)==2:yield base+'Completion',calls._composition(base,obj,role_prefix='remaining')
