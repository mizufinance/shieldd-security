"""Actual input-note sponge boundaries and bounded all-lane source/row matcher.

The accepted two-note source packet is mandatory. Each call uses domain+arity
IVs and exact adjacent absorption LCs. Tree child routing remains a separate
obligation; merely capturing a state hash does not prove Merkle membership.
"""
import hashlib
from . import transfer_relation as relation,transfer_note_spend as notes,poseidon_graph,transfer_arithmetic as arithmetic
from .transfer_authorization_roles import _expressions
from .transfer_balance_rows import canonical,combine,source_index

P=relation.MODULUS
SCOPE='one input-note permutation cone and two note source LCs; tree wiring and native joins open'


def inspect_boundaries(data,note_data,accepted_roles):
    accepted=notes.inspect_metadata(note_data,accepted_roles)
    if not isinstance(data,bytes) or len(data)>4*1024*1024:
        raise relation.RelationError('note hash metadata byte bound')
    obj=relation.record(data)
    keys={'schema','family','scope','relation_digest','domain_size','full_rows','constant_copy',
          'ordinary_full_ordered_rows_equal','repeated_observations_equal','slot','role','level','block','hash','expressions','nodes'}
    if set(obj)!=keys or (obj['schema'],obj['family'],obj['scope'])!=('shieldd-transfer-note-hash-block-v1','transfer',SCOPE):
        raise relation.RelationError('note hash closed schema/scope mismatch')
    if (any(obj[k]!=accepted['metadata'][k] for k in ('relation_digest','domain_size','full_rows','constant_copy')) or
        obj['ordinary_full_ordered_rows_equal'] is not True or obj['repeated_observations_equal'] is not True):
        raise relation.RelationError('note hash identity/pending parity mismatch')
    slot=relation.natural(obj['slot'],2);role=obj['role'];level=relation.natural(obj['level'],24)
    if role not in ('commitment','nullifier','dummy','state') or (role!='state' and level) or (role=='dummy' and slot!=1):
        raise relation.RelationError('note hash native role/level policy mismatch')
    block=relation.natural(obj['block'],2 if role=='commitment' else 1)
    observed=_expressions(obj['expressions'],obj['domain_size'],obj['constant_copy'],4096,'note hash')
    for handle,lc in accepted['observed'].items():
        if observed.get(handle)!=lc:raise relation.RelationError('note hash accepted two-note source LC mismatch')
    required=set(accepted['observed'])
    def value(ref):
        if not isinstance(ref,dict) or len(ref)!=1:raise relation.RelationError('note hash reference shape')
        if set(ref)=={'source'}:
            handle=source_index(ref['source']);required.add(handle)
            if handle not in observed:raise relation.RelationError('note hash missing source LC')
            return observed[handle]
        if set(ref)=={'native'}:
            encoded=ref['native']
            if not isinstance(encoded,str) or len(encoded)!=64 or any(c not in '0123456789abcdef' for c in encoded) or int(encoded,16)>=P:
                raise relation.RelationError('note hash native encoding')
            return canonical([(0,int(encoded,16))])
        raise relation.RelationError('note hash unknown source reference')
    call=obj['hash'];domain,arity,count={'commitment':(15,8,2),'nullifier':(7,3,1),'dummy':(22,3,1),'state':(1,5,1)}[role]
    if (not isinstance(call,dict) or set(call)!={'domain','inputs','output','blocks'} or
        type(call['domain']) is not int or call['domain']!=domain or not isinstance(call['inputs'],list) or len(call['inputs'])!=arity or
        not isinstance(call['blocks'],list) or len(call['blocks'])!=count):
        raise relation.RelationError('note hash native domain/arity/block mismatch')
    inputs=[value(ref) for ref in call['inputs']];output=value(call['output'])
    spend=accepted['metadata']['spends'][slot]
    if role=='commitment':wanted,wanted_output=spend['note'],spend['commitment']
    elif role=='nullifier':wanted,wanted_output=[spend['shared']['nk'],spend['commitment'],spend['position']],spend['real_nullifier']
    elif role=='dummy':wanted,wanted_output=[spend['optional']['seed'],spend['shared']['randomizer'],{'native':f'{1:064x}'}],spend['optional']['synthetic']
    else:
        wanted,wanted_output=None,spend['computed_anchor'] if level==23 else None
        if call['inputs'][0]!={'native':f'{level+1:064x}'}:raise relation.RelationError('note state level prefix mismatch')
    if (wanted is not None and call['inputs']!=wanted) or (wanted_output is not None and call['output']!=wanted_output):
        raise relation.RelationError('note hash accepted source role mismatch')
    state=[canonical([(0,domain+256*arity)]),(),(),(),(),()]
    for index,part in enumerate(call['blocks']):
        if not isinstance(part,dict) or set(part)!={'before','after'} or any(not isinstance(part[k],list) or len(part[k])!=6 for k in ('before','after')):
            raise relation.RelationError('note hash permutation width mismatch')
        before=[value(ref) for ref in part['before']];after=[value(ref) for ref in part['after']]
        expected=list(state)
        for lane,item in enumerate(inputs[5*index:5*(index+1)],1):expected[lane]=combine(expected[lane],item)
        if before!=expected:raise relation.RelationError('note hash absorbed state LC mismatch')
        state=after
    if output!=state[1] or call['output']!=call['blocks'][-1]['after'][1]:
        raise relation.RelationError('note hash output lane/source mismatch')
    return dict(metadata=obj,observed=observed,boundary_sources=required,block=block,
                metadata_sha256=hashlib.sha256(data).hexdigest())


def inspect_metadata(data,note_data,accepted_roles,parameter_root):
    return _inspect_permutation(inspect_boundaries(data,note_data,accepted_roles),parameter_root)


def _inspect_permutation(checked,parameter_root,*,width=6):
    """Reuse the bounded DAG check only after exact native-role acceptance."""
    if width not in (3,6):raise relation.RelationError('actual permutation width policy')
    obj=checked['metadata'];observed=checked['observed']
    part=obj['hash']['blocks'][checked['block']];before,after=part['before'],part['after']
    if len(before)!=width or len(after)!=width:raise relation.RelationError('actual permutation checkpoint width')
    boundaries=[source_index(ref['source']) for ref in before if 'source' in ref]
    if len(set(boundaries))!=len(boundaries):raise relation.RelationError('aliased note permutation inputs')
    if any(set(ref)!={'source'} for ref in after):raise relation.RelationError('native note permutation output')
    outputs=[source_index(ref['source']) for ref in after]
    table={};previous=-1
    if not isinstance(obj['nodes'],list) or len(obj['nodes'])>16384:raise relation.RelationError('note permutation node bound')
    for node in obj['nodes']:
        if not isinstance(node,dict) or set(node)!={'index','multiply','left','right'}:raise relation.RelationError('note permutation node shape')
        index=relation.natural(node['index'],2**32)
        if index<=previous or type(node['multiply']) is not bool:raise relation.RelationError('note permutation node order/type')
        previous=index;left,right=source_index(node['left']),source_index(node['right'])
        if any(tag==2 and child>=index for tag,child in (left,right)):raise relation.RelationError('note permutation forward edge')
        table[(2,index)]=(node['multiply'],left,right)
    visited=set();pending=list(outputs)
    while pending:
        ref=pending.pop()
        if ref in visited:continue
        visited.add(ref)
        if len(visited)>16384:raise relation.RelationError('note permutation cone bound')
        if ref in boundaries:continue
        if ref[0]==2:
            if ref not in table:raise relation.RelationError('note permutation missing source node')
            pending.extend(table[ref][1:])
        elif ref[0]==0:
            if ref not in observed:raise relation.RelationError('note permutation missing constant')
        else:raise relation.RelationError('note permutation undeclared witness')
    if set(table)!={ref for ref in visited if ref[0]==2 and ref not in boundaries}:raise relation.RelationError('note permutation extra source node')
    required=checked['boundary_sources']|{ref for ref in visited if ref[0]==0}
    for ref,(multiply,left,right) in table.items():
        if multiply and left[0]!=0 and right[0]!=0:required.update((ref,left,right))
    if set(observed)!=required:raise relation.RelationError('note permutation exact LC coverage mismatch')
    names={ref:f'w{index}' for index,ref in enumerate(boundaries)}
    def name(ref):return names.get(ref,'cwn'[ref[0]]+str(ref[1]))
    abstract={names[ref]:dict(kind='witness') for ref in boundaries};derived={ref:observed[ref] for ref in boundaries}
    for ref in sorted(visited):
        if ref in boundaries:continue
        if ref[0]==0:
            lc=observed[ref];abstract[name(ref)]=dict(kind='constant',value=lc[0][1] if lc else 0);derived[ref]=lc;continue
        multiply,left,right=table[ref]
        abstract[name(ref)]=dict(kind='mul' if multiply else 'add',left=name(left),right=name(right))
        if multiply:
            folded=None
            for scalar,other in ((derived[left],derived[right]),(derived[right],derived[left])):
                if all(c==0 for c,_ in scalar):folded=canonical((c,v*(scalar[0][1] if scalar else 0)) for c,v in other);break
            if folded is None:
                if ref not in observed:raise relation.RelationError('note permutation missing nonlinear output LC')
                folded=observed[ref]
        else:folded=combine(derived[left],derived[right])
        derived[ref]=folded
        if ref in observed and observed[ref]!=folded:raise relation.RelationError('note permutation source/compiler LC mismatch')
    params=poseidon_graph.parameters(parameter_root/('poseidon381.json' if width==3 else 'poseidon381-wide.json'),width)
    graph=poseidon_graph.permutation(params,[int(ref['native'],16) if 'native' in ref else None for ref in before])
    try:pairs=poseidon_graph.match_permutation(graph,abstract,[names[ref] for ref in boundaries],[name(ref) for ref in outputs])
    except ValueError as error:raise relation.RelationError('note permutation source mismatch: '+str(error)) from error
    if {actual for _,actual in pairs}!=set(abstract):raise relation.RelationError('note permutation unmatched source cone')
    checked.update(nodes=table,derived=derived,graph=graph,pairs=pairs,source=abstract,source_names={ref:name(ref) for ref in visited},inputs=boundaries,outputs=outputs)
    return checked


def extract(data,stream,note_data,accepted_roles,parameter_root):
    return _extract_permutation(inspect_metadata(data,note_data,accepted_roles,parameter_root),stream)


def _extract_permutation(checked,stream,*,label='note-hash'):
    obj=checked['metadata'];copy=obj['constant_copy']
    outline=lambda lc:canonical((copy if c==0 else c,v) for c,v in lc)
    required={(canonical([(0,1),(copy,-1)]),()):['constant-copy']};products=[]
    for ref,(multiply,left,right) in checked['nodes'].items():
        if not multiply:continue
        a,b,z=(checked['derived'][r] for r in (left,right,ref))
        if any(all(c==0 for c,_ in lc) for lc in (a,b)):continue
        role='node.'+str(ref[1])
        if a==b:required.setdefault((outline(a),outline(z)),[]).append(role)
        else:products.append((role,outline(combine(a,b,-1)),outline(combine(a,b)),outline(z),None))
    extracted=arithmetic.extract_templates(stream,obj['relation_digest'],obj['domain_size'],obj['full_rows'],required,products,[],label=label)
    extracted.update(metadata_sha256=checked['metadata_sha256'],slot=obj['slot'],role=obj['role'],level=obj['level'],block=obj['block'],
                     scope='actual one note permutation rows only; kernel and complete hash/native joins open')
    return extracted


def round_selection(data,extracted,note_data,accepted_roles,parameter_root):
    """Adapt exact note rows to the maintained Poseidon round generator."""
    return _select_permutation(inspect_metadata(data,note_data,accepted_roles,parameter_root),extracted,parameter_root)


def _select_permutation(checked,extracted,parameter_root,*,role_prefix='spend'):
    obj=checked['metadata']
    if any(extracted.get(k)!=obj[k] for k in ('slot','role','level','block')):
        raise relation.RelationError('note hash extraction role mismatch')
    raw,normalized=arithmetic.normalize_selection(extracted,obj,checked['metadata_sha256'])
    used=set()
    for ref,(multiply,left,right) in checked['nodes'].items():
        if multiply:
            certificate=arithmetic.product_certificate(*(checked['derived'][r] for r in (left,right,ref)),normalized)
            used.update(certificate['rows'])
    link=next(i for i,pair in raw.items() if pair==(canonical([(0,1),(obj['constant_copy'],-1)]),()))
    if used|{link}!=set(raw):raise relation.RelationError('note hash exact physical row coverage mismatch')
    observations={checked['source_names'][ref]:lc for ref,lc in checked['derived'].items()}
    matches={}
    for expected,actual in checked['pairs']:matches.setdefault(expected,set()).add(actual)
    graph=checked['graph'];cache={}
    def terms(index):
        if index not in cache:
            if index in matches:
                values={observations[actual] for actual in matches[index]}
                if len(values)!=1:raise relation.RelationError('note hash unequal shared graph LC')
                cache[index]=next(iter(values))
            elif graph['nodes'][index]['kind']=='constant':cache[index]=canonical([(0,graph['nodes'][index]['value'])])
            else:raise relation.RelationError('note hash unmatched round graph node')
        return cache[index]
    segments=[]
    for segment in graph['segments']:
        fifths={};rows=set()
        for lane,power in segment['powers'].items():
            base=terms(segment['shifted'][lane]);transformed=terms(segment['transformed'][lane])
            if all(c==0 for c,_ in base):
                coefficient=base[0][1] if base else 0
                if transformed!=canonical([(0,pow(coefficient,5,P))]):raise relation.RelationError('note hash native fifth mismatch')
                fifths[lane]=dict(kind='constant',coefficient=coefficient);continue
            square,fourth=terms(power['square']),terms(power['fourth'])
            square_cert=arithmetic.product_certificate(base,base,square,normalized)
            fourth_cert=arithmetic.product_certificate(square,square,fourth,normalized)
            fifth_cert=arithmetic.product_certificate(fourth,base,transformed,normalized)
            if fifth_cert['kind']!='product' or fifth_cert['swapped']:
                raise relation.RelationError('note hash fifth round requires owned oriented product rows')
            indices=square_cert['rows']+fourth_cert['rows']+fifth_cert['rows'];rows.update(indices)
            fifths[lane]=dict(kind='arithmetic',square=square,fourth=fourth,auxiliary=fifth_cert['auxiliary'],rows=indices)
        segments.append(dict(kind='round',chunk=0,index=segment['round'],before=[terms(i) for i in segment['before']],
            shifted=[terms(i) for i in segment['shifted']],transformed=[terms(i) for i in segment['transformed']],
            after=[terms(i) for i in segment['after']],fifths=fifths,rows=sorted(rows)))
    width=graph['width']
    params=poseidon_graph.parameters(parameter_root/('poseidon381.json' if width==3 else 'poseidon381-wide.json'),width)
    role=f"{role_prefix}{obj['slot']}.{obj['role']}{obj['level']}.permutation{obj['block']}"
    call=dict(graph={**graph,'domain':obj['hash']['domain']},
              inputs=[checked['source_names'][ref] for ref in checked['inputs']],output=checked['source_names'][checked['outputs'][1]])
    return dict(outline=obj['constant_copy'],constant_link=link,rows=raw,
        calls=[dict(role=role,segments=segments,parameters=params,call=call)],
        observations={name:('linear',lc) for name,lc in observations.items()},
        scope='one actual note permutation; absorption/native/tree joins remain separate')
