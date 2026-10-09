"""Actual receiver131 range and67 enabled-status assertion row selection.

Source roles are independently accepted from the qualified receiver19 pages.
Product outputs/auxiliaries are inferred only from unique physical row pairs,
not from source handle arithmetic or an assumed enabled-bit value. This does
not supply native lifecycle or subgroup/source-object interpretation.
"""
import hashlib
from . import transfer_remaining_pages as pages, transfer_relation as relation
from . import transfer_arithmetic as arithmetic
from .transfer_balance_rows import canonical, combine, source_index
from .transfer_note_ranges import _generate_boundary
from .generate_hash_round import linear, _signature_audits

MAX_ASSERTIONS = 16384
MAX_CANDIDATES = 256
SCOPE = 'actual131 range and67 enabled status/high-zero products; native lifecycle/subgroup joins open'

def boundary(manifest_data, role_data, accepted_roles):
    checked=pages.inspect_page(manifest_data,role_data,0,accepted_roles)
    if checked['metadata']['scope']!='receiver':raise relation.RelationError('receiver lifecycle exact receiver roles')
    refs=checked['records']['receiver','lifecycle-bits',0]
    value_ref=checked['records']['receiver','receiver-binding',0][7]
    regulated_ref=checked['records']['receiver','membership',0][4]
    at=lambda ref:checked['observed'][source_index(ref['source'])]
    bits=[at(ref) for ref in refs];value=at(value_ref);regulated=at(regulated_ref)
    if len(value)!=1 or value[0][1]!=1 or any(len(bit)!=1 or bit[0][1]!=1 for bit in bits):
        raise relation.RelationError('receiver lifecycle unit scalar/131 bit LCs')
    columns=[bit[0][0] for bit in bits]
    if len(columns)!=131 or columns!=list(range(columns[0],columns[0]+131)) or value[0][0] in columns:
        raise relation.RelationError('receiver lifecycle exact disjoint contiguous131 layout')
    owned={source_index(ref['source']) for ref in refs}
    readonly={c for handle,lc in checked['observed'].items() if handle not in owned for c,_ in lc}
    readonly.update(c for lc in accepted_roles['observed'].values() for c,_ in lc)
    if set(columns)&readonly:raise relation.RelationError('receiver lifecycle bits alias another source consumer')
    gates=[dict(index=i,expected=1 if i==0 else 0,left=regulated,
                right=combine(bits[i],((0,1),),-1) if i==0 else bits[i])
           for i in [0,1,2,*range(67,131)]]
    return dict(checked=checked,columns=columns,value=value[0][0],width=131,
        weighted=canonical((c,2**i) for i,c in enumerate(columns)),slot=0,kind='lifecycle',
        owned_handles=owned,regulated=regulated,gates=gates,
        protected=sorted(readonly|set(columns)|{0,1,2,checked['metadata']['constant_copy']}))

def _requirements(selected):
    copy=selected['checked']['metadata']['constant_copy']
    outline=lambda lc:canonical((copy if c==0 else c,v) for c,v in lc)
    direct={(canonical([(0,1),(copy,-1)]),()):['constant-copy']}
    for i,c in enumerate(selected['columns']):direct[(((c,1),),((c,1),))]=['bit.'+str(i)]
    direct[(outline(combine(selected['weighted'],((selected['value'],1),),-1)),())]=['reconstruction']
    requests=[]
    for gate in selected['gates']:
        left,right=outline(gate['left']),outline(gate['right'])
        if not left or not right or left==right:raise relation.RelationError('receiver lifecycle unsupported folded/square gate')
        requests.append((gate,combine(left,right,-1),combine(left,right)))
    return direct,requests

def _match(direct,requests,candidates,assertions):
    matched={};gates=[];used=set()
    for key,roles in direct.items():
        matches=candidates.get(key,[])
        if len(matches)!=1:raise relation.RelationError('receiver lifecycle unique direct row '+roles[0])
        matched[key]=matches[0]['row'];used.add(matches[0]['row'])
    for gate,minus,plus in requests:
        found=[]
        for first in candidates.get((minus,None),[])+candidates.get((canonical((c,-v) for c,v in minus),None),[]):
            auxiliary=tuple((c,int(v,16)) for c,v in first['b'])
            if len(auxiliary)!=1 or auxiliary[0][1]!=1:continue
            for second in candidates.get((plus,None),[]):
                if first['row']>=second['row']:continue
                output=canonical((c,v*pow(4,-1,relation.MODULUS)) for c,v in combine(
                    tuple((c,int(v,16)) for c,v in second['b']),auxiliary,-1))
                if not output:equalities=[None]
                elif len(output)==1 and output[0][1]==1:
                    equalities=assertions.get(output,[])+assertions.get(canonical((c,-v) for c,v in output),[])
                else:continue
                for assertion in equalities:
                    if assertion is not None and second['row']>=assertion['row']:continue
                    found.append(dict(index=gate['index'],expected=gate['expected'],
                        rows=[first['row'],second['row']]+([] if assertion is None else [assertion['row']]),
                        auxiliary=auxiliary,output=output,swapped=tuple((c,int(v,16)) for c,v in first['a'])!=minus))
        if len(found)!=1:raise relation.RelationError('receiver lifecycle unique exact gate '+str(gate['index']))
        gates.append(found[0]);used.update(found[0]['rows'])
    return matched,gates,used

def _retain(stream,selected):
    obj=selected['checked']['metadata'];direct,requests=_requirements(selected)
    targets={lc for _,minus,plus in requests for lc in (minus,canonical((c,-v) for c,v in minus),plus)}
    candidates={};assertions={};rows={};assertion_count=0
    def observe(row):
        nonlocal assertion_count
        a,b=(tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b'))
        key=(a,b)
        if key not in direct:key=(canonical((c,-v) for c,v in a),b)
        if key in direct:candidates.setdefault(key,[]).append(row);rows[row['row']]=row
        if a in targets:
            candidates.setdefault((a,None),[]).append(row);rows[row['row']]=row
            if len(candidates[a,None])>MAX_CANDIDATES:raise relation.RelationError('receiver lifecycle candidate bound')
        if not b and len(a)==1:
            assertions.setdefault(a,[]).append(row)
            assertion_count+=1
            if assertion_count>MAX_ASSERTIONS:
                raise relation.RelationError('receiver lifecycle assertion candidate bound')
    identity=relation.inspect(stream,expected_relation=obj['relation_digest'],row_observer=observe)
    if (identity['domain_size'],identity['stored_rows'])!=(obj['domain_size'],obj['full_rows']):
        raise relation.RelationError('receiver lifecycle exact full ordinary shape')
    matched,gates,used=_match(direct,requests,candidates,assertions)
    for entries in assertions.values():
        for row in entries:
            if row['row'] in used:rows[row['row']]=row
    return dict(identity=identity,templates=[dict(roles=roles,row=matched[key]) for key,roles in direct.items()],
        gates=gates,selected_rows=[rows[i] for i in sorted(used)])

def extract(manifest_data,role_data,stream,accepted_roles):
    selected=boundary(manifest_data,role_data,accepted_roles)
    result=_retain(stream,selected)
    result.update(schema='shieldd-transfer-receiver-lifecycle-rows-v1',
        metadata_sha256=hashlib.sha256(role_data).hexdigest(),manifest_sha256=hashlib.sha256(manifest_data).hexdigest(),
        slot=0,kind='lifecycle',scope=SCOPE)
    validate(manifest_data,role_data,result,accepted_roles)
    return result

def validate(manifest_data,role_data,extracted,accepted_roles):
    selected=boundary(manifest_data,role_data,accepted_roles);obj=selected['checked']['metadata']
    if not isinstance(extracted,dict) or set(extracted)!={'schema','manifest_sha256','metadata_sha256','slot','kind','scope','identity','templates','gates','selected_rows'} or extracted.get('scope')!=SCOPE:
        raise relation.RelationError('receiver lifecycle closed extraction shape')
    if (extracted.get('schema'),extracted.get('manifest_sha256'),extracted.get('slot'),extracted.get('kind'))!=('shieldd-transfer-receiver-lifecycle-rows-v1',hashlib.sha256(manifest_data).hexdigest(),0,'lifecycle'):
        raise relation.RelationError('receiver lifecycle retained scope/manifest identity')
    raw,normalized=arithmetic.normalize_selection(extracted,obj,hashlib.sha256(role_data).hexdigest())
    direct,requests=_requirements(selected);candidates={};assertions={}
    for row in extracted['selected_rows']:
        a,b=raw[row['row']];key=(a,b)
        if key not in direct:key=(canonical((c,-v) for c,v in a),b)
        if key in direct:candidates.setdefault(key,[]).append(row)
        candidates.setdefault((a,None),[]).append(row)
        if not b:assertions.setdefault(a,[]).append(row)
    matched,gates,used=_match(direct,requests,candidates,assertions)
    # JSON arrays are normalized only after strict LC/row parsing above.
    normalized_gates=[]
    for gate in extracted.get('gates',[]):
        if not isinstance(gate,dict) or set(gate)!={'index','expected','rows','auxiliary','output','swapped'} or type(gate['swapped'])is not bool:
            raise relation.RelationError('receiver lifecycle gate closed shape')
        relation.natural(gate['index'],131);relation.natural(gate['expected'],2)
        if not isinstance(gate['rows'],list) or len(gate['rows']) not in (2,3):raise relation.RelationError('receiver lifecycle gate row shape')
        for index in gate['rows']:relation.natural(index,obj['full_rows'])
        for lc in (gate['auxiliary'],gate['output']):
            if not isinstance(lc,(list,tuple)):raise relation.RelationError('receiver lifecycle derivative LC shape')
            for term in lc:
                if not isinstance(term,(list,tuple)) or len(term)!=2:raise relation.RelationError('receiver lifecycle derivative term shape')
                relation.natural(term[0],obj['domain_size']);relation.natural(term[1],relation.MODULUS)
        normalized_gates.append({**gate,'auxiliary':tuple(tuple(term) for term in gate['auxiliary']),
            'output':tuple(tuple(term) for term in gate['output'])})
    if gates!=normalized_gates or used!=set(raw) or extracted['templates']!=[dict(roles=roles,row=matched[key]) for key,roles in direct.items()]:
        raise relation.RelationError('receiver lifecycle exact retained physical coverage')
    writes=[]
    for gate in gates:
        own=[gate['auxiliary'][0][0]]+([gate['output'][0][0]] if gate['output'] else [])
        if len(set(own))!=len(own) or set(own)&set(selected['protected']) or set(own)&set(writes):
            raise relation.RelationError('receiver lifecycle exact fresh gate writes/source-consumer exclusion')
        writes.extend(own)
    selected.update(raw=raw,normalized=normalized,gate_certificates=gates,writes=writes)
    return selected

def generate_range(manifest_data,role_data,extracted,accepted_roles):
    selected=validate(manifest_data,role_data,extracted,accepted_roles)
    indices={item['row'] for item in extracted['templates']}
    part={**extracted,'selected_rows':[row for row in extracted['selected_rows'] if row['row'] in indices]}
    return _generate_boundary(role_data,part,accepted_roles,selected,0,'lifecycle',selected['owned_handles'],
                              'RuntimeTransferReceiverLifecycleRange')

def generate_gate(manifest_data,role_data,extracted,accepted_roles,ordinal):
    selected=validate(manifest_data,role_data,extracted,accepted_roles)
    ordinal=relation.natural(ordinal,len(selected['gates']));gate=selected['gates'][ordinal];cert=selected['gate_certificates'][ordinal]
    copy=selected['checked']['metadata']['constant_copy'];copy_index=next(t['row'] for t in extracted['templates'] if t['roles']==['constant-copy'])
    raw={index:selected['raw'][index] for index in sorted({copy_index,*cert['rows']})}
    left,right=gate['left'],gate['right']
    if cert['swapped']:left,right=right,left
    ns=f'RuntimeTransferReceiverLifecycleGate{gate["index"]:03}'
    source=f'''import ShielddSecurity.Compiler
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
namespace ShielddSecurity.{ns}
def modulus : Nat := {relation.MODULUS}
def originalRows : List Nat := {list(raw)}
def rawRows : List Row := [
'''+',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in raw.values())+f''']
def rows : List Row := Compiler.unoutlineRows {copy} rawRows
def left : Linear := {linear(left)}
def right : Linear := {linear(right)}
def output : Linear := {linear(cert['output'])}
def auxiliary : Linear := {linear(cert['auxiliary'])}
theorem constantLink : Compiler.checkRow modulus rawRows ⟨[(0,1),({copy},-1)],[]⟩ = true := by decide
theorem actual_gate {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho rawRows) :
    eval rho left * eval rho right = 0 := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied constantLink
  have product := Compiler.checked_product_sound rho rows left right output auxiliary four normalized (by decide) (by decide)
'''
    if cert['output']:
        source+='''  have asserted := Compiler.checked_assertion_sound rho rows output [] normalized (by decide)
  have zero : eval rho output = 0 := by simpa only [eval] using asserted
  exact product.symm.trans zero
'''
    else:source+='''  simpa only [output,eval] using product.symm
'''
    source+=f'''#print axioms constantLink
#print axioms actual_gate
end ShielddSecurity.{ns}
'''
    return ns,_signature_audits(source)
