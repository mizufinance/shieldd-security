"""Strict routing precision and permutation row derivatives.

Missing source handles are never guessed. Unit operands are inferred only
from unique original physical templates. The caller owns the single full-row
replay; retained generation does not establish native routing or UserSem.
"""
import hashlib,json
from . import transfer_remaining_pages as pages,transfer_arithmetic as arithmetic
from . import transfer_relation as relation
from .transfer_fixed_spend import canonical,combine

ONE=((0,1),)
# A complete bounded pool must accommodate the pinned 200770-row relation.
# These are extraction limits, not claims about the routing witness layout.
MAX_ROWS=262144
MAX_TERMS=2097152
SCHEMA='shieldd-transfer-routing-row-derivative-v1'


def boundaries(manifest_data,role_page,permutation_page,accepted_roles,parameter_root):
    manifest=pages.inspect_manifest(manifest_data,accepted_roles['metadata']['relation_digest'])
    if manifest['scope']!='routing' or len(manifest['pages'])!=7:
        raise relation.RelationError('exact seven-page routing scope')
    role=pages.inspect_page(manifest_data,role_page,0,accepted_roles)
    permutation=pages.inspect_page(manifest_data,permutation_page,4,accepted_roles,parameter_root)
    if (role['metadata']['records']!=permutation['metadata']['records'] or role['metadata']['calls']!=permutation['metadata']['calls']
            or any(role['metadata'][k]!=permutation['metadata'][k] for k in pages.IDENTITY)
            or permutation['metadata']['hash']['domain']!=32):
        raise relation.RelationError('same exact routing source objects/permutation')
    for handle in role['observed'].keys()&permutation['observed'].keys():
        if role['observed'][handle]!=permutation['observed'][handle]:raise relation.RelationError('routing cross-page LC changed')
    def value(ref,checked=role):
        kind,handle=pages.reference(ref)
        return canonical([(0,handle)]) if kind=='native' else checked['observed'][handle]
    records=role['records'];precision=[]
    for slot,tag in enumerate(('regulated-prefix','unregulated-prefix')):
        prefix=[value(ref) for ref in records['routing',tag,0]]
        matches=[combine(prefix[i-1],prefix[i],-1) for i in range(1,32)]+[prefix[31]]
        columns=[_unit(lc,'precision prefix difference') for lc in matches]
        input_lc=value(records['routing','precision-values',0][slot])
        if len(set(columns))!=32 or set(columns)&{0,role['metadata']['constant_copy']}:
            raise relation.RelationError('precision distinct captured match1..32 operands')
        precision.append(dict(input=input_lc,prefix=prefix,known_matches=matches))
    swapped=value(records['routing','flags',0][0]);_unit(swapped,'permutation low bit')
    output=value(permutation['metadata']['hash']['output'],permutation)
    digest=hashlib.sha256(len(role_page).to_bytes(8,'big')+role_page+len(permutation_page).to_bytes(8,'big')+permutation_page).hexdigest()
    return dict(checked=role,permutation=permutation,precision=precision,swapped=swapped,output=output,metadata_sha256=digest,
                role_page_sha256=hashlib.sha256(role_page).hexdigest(),permutation_page_sha256=hashlib.sha256(permutation_page).hexdigest())


def _unit(lc,label):
    if len(lc)!=1 or lc[0][1]!=1 or lc[0][0]==0:
        raise relation.RelationError('actual fresh unit LC required: '+label)
    return lc[0][0]


class _Rows:
    def __init__(self,raw,normalized,copy):
        self.raw=raw;self.normalized=normalized;self.by_a={};self.by_row={};self.copy=copy
        for index,(a,b) in normalized.items():
            self.by_a.setdefault(a,[]).append((b,index));self.by_row.setdefault((a,b),[]).append(index)
    def exact(self,a,b,label,signed=False):
        matches=list(self.by_row.get((a,b),[]));negative=canonical((c,-v) for c,v in a)
        if signed and negative!=a:matches+=self.by_row.get((negative,b),[])
        if len(matches)!=1:raise relation.RelationError('unique physical routing row required: '+label)
        return matches[0]
    def pairs(self,left,right):
        minus=combine(left,right,-1);plus=combine(left,right);found=[]
        for swapped,a in ((False,minus),(True,canonical((c,-v) for c,v in minus))):
            if swapped and a==minus:continue
            for auxiliary,first in self.by_a.get(a,[]):
                for total,second in self.by_a.get(plus,[]):
                    if first>=second:continue
                    output=canonical((c,v*pow(4,-1,relation.MODULUS)) for c,v in combine(total,auxiliary,-1))
                    found.append(dict(output=output,auxiliary=auxiliary,swapped=swapped,rows=[first,second]))
        return found
    def products(self,left,right,numerator=None):
        found=[]
        for pair in self.pairs(left,right):
            if numerator is not None:
                equation=combine(pair['output'],numerator,-1)
                if not equation:continue
                indices=list(self.by_row.get((equation,()),[]));negative=canonical((c,-v) for c,v in equation)
                if negative!=equation:indices+=self.by_row.get((negative,()),[])
                for index in indices:found.append({**pair,'rows':pair['rows']+[index]})
            else:found.append(pair)
        unique={json.dumps(item,sort_keys=True,separators=(',',':')):item for item in found}
        return list(unique.values())
    def product(self,left,right,label,numerator=None):
        found=self.products(left,right,numerator)
        if len(found)!=1:raise relation.RelationError('unique physical routing product required: '+label)
        return found[0]


def _precision(selected,table,slot):
    known=selected['known_matches'];total=()
    for lc in known:total=combine(total,lc)
    occupied={c for lc in known+[selected['input']] for c,v in lc}|{0,table.copy}
    candidates=[]
    for index,(a,b) in table.normalized.items():
        if b:continue
        for orientation in (1,-1):
            actual=canonical((c,v*orientation) for c,v in a)
            missing=combine(combine(actual,total,-1),ONE)
            if len(missing)==1 and missing[0][1]==1 and missing[0][0] not in occupied:
                if len(table.by_row.get((missing,missing),[]))==1:candidates.append((missing,index))
    candidates=list(dict.fromkeys(candidates))
    if len(candidates)!=1:raise relation.RelationError('unique actual precision match0/onehot assertion required')
    missing,onehot=candidates[0];matches=[missing,*known];occupied|={missing[0][0]};steps=[];used={onehot}
    for value,zero in enumerate(matches):
        denominator=combine(selected['input'],((0,value),) if value else (),-1)
        boolean=table.exact(zero,zero,'precisionBoolean'+str(slot)+'.'+str(value));used.add(boolean)
        inverses=[]
        for a in table.by_a:
            for sign in (1,-1):
                inverse=combine(denominator,a,-sign)
                if len(inverse)!=1 or inverse[0][1]!=1 or inverse[0][0] in occupied:continue
                for product in table.products(denominator,inverse,combine(ONE,zero,-1)):
                    inverses.append(dict(inverse=inverse,product=product))
        unique={json.dumps(item,sort_keys=True,separators=(',',':')):item for item in inverses}
        if len(unique)!=1:raise relation.RelationError('unique actual precision inverse operand required: '+str(value))
        inverse=next(iter(unique.values()));zero_product=table.product(denominator,zero,'precision zero product',())
        used.update(inverse['product']['rows']);used.update(zero_product['rows'])
        steps.append(dict(value=value,denominator=denominator,zero=zero,boolean_row=boolean,
                          inverse=inverse['inverse'],inverse_product=inverse['product'],zero_product=zero_product))
    if len({step['inverse'][0][0] for step in steps})!=33:
        raise relation.RelationError('actual precision inverse allocations must be distinct')
    return dict(input=selected['input'],matches=matches,prefix=selected['prefix'],onehot_row=onehot,steps=steps),used


def _permutation(selected,table):
    weights={pow(2,i,relation.MODULUS):i for i in range(255)}
    if len(weights)!=255:raise relation.RelationError('distinct canonical255 field weights required')
    bit0=_unit(selected['swapped'],'captured swapped bit');occupied={c for c,v in selected['output']}|{0,table.copy};found=[]
    for index,(a,b) in table.normalized.items():
        if b or not any(c==bit0 for c,v in a):continue
        for sign in (1,-1):
            weighted=combine(canonical((c,v*sign) for c,v in a),selected['output'])
            if len(weighted)!=255 or any(v not in weights or c in occupied for c,v in weighted):continue
            bits=[None]*255
            for column,coefficient in weighted:
                if bits[weights[coefficient]] is not None:break
                bits[weights[coefficient]]=column
            if any(column is None for column in bits) or bits[0]!=bit0 or len(set(bits))!=255:continue
            if any(len(table.by_row.get((((column,1),),((column,1),)),[]))!=1 for column in bits):continue
            found.append((tuple(bits),index))
    found=list(dict.fromkeys(found))
    if len(found)!=1:raise relation.RelationError('unique actual canonical255 reconstruction/bit operands required')
    columns,reconstruction=found[0];before=ONE;steps=[];used={reconstruction}
    for index,column in enumerate(columns):
        left=((column,1),);right=((relation.MODULUS-1)>>index)&1
        both=combine(ONE,left,-1) if right else ()
        factor=combine(combine(combine(ONE,left,-1),((0,right),) if right else ()),both,-2)
        boolean=table.exact(left,left,'permutationBoolean'+str(index));used.add(boolean)
        if index==0:product=factor;certificate=dict(kind='folded',rows=[])
        else:
            certificate=table.product(before,factor,'canonical255 comparator'+str(index));product=certificate['output'];used.update(certificate['rows'])
        after=combine(both,product);steps.append(dict(before=before,left=left,right=right,factor=factor,product=product,after=after,certificate=certificate,boolean_row=boolean));before=after
    final_boolean=table.exact(before,before,'canonical255 comparison Boolean');used.add(final_boolean)
    endpoint=table.exact(combine(before,ONE,-1),(),'canonical255 endpoint',True);used.add(endpoint)
    return dict(columns=list(columns),output=selected['output'],swapped=selected['swapped'],reconstruction_row=reconstruction,
                maximum=relation.MODULUS-1,steps=steps,final_boolean_row=final_boolean,endpoint_row=endpoint),used


def _plan(selected,raw,normalized):
    copy=selected['checked']['metadata']['constant_copy'];table=_Rows(raw,normalized,copy)
    links=[i for i,row in raw.items() if row==(canonical([(0,1),(copy,-1)]),())]
    if len(links)!=1:raise relation.RelationError('unique routing constant-copy link required')
    used={links[0]};precision=[]
    for slot,item in enumerate(selected['precision']):
        result,part=_precision(item,table,slot);precision.append(result);used.update(part)
    permutation,part=_permutation(selected,table);used.update(part)
    return dict(precision=precision,permutation=permutation,constant_link=links[0]),used


def extract(manifest_data,role_page,permutation_page,stream,accepted_roles,parameter_root):
    """Root-only one full ordered replay, bounded pool, then strict inference."""
    selected=boundaries(manifest_data,role_page,permutation_page,accepted_roles,parameter_root)
    metadata=selected['checked']['metadata'];copy=metadata['constant_copy'];raw={};normalized={};terms=0
    precision_columns={c for item in selected['precision'] for lc in [item['input'],*item['known_matches']] for c,v in lc}
    bit0=_unit(selected['swapped'],'permutation low bit')
    def observe(row):
        nonlocal terms
        a,b=(tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b'))
        touches=any(c in precision_columns or c==bit0 for c,v in a)
        boolean=a==b and len(a)==1 and a[0][1]==1
        small=len(a)<=6 and len(b)<=6
        if not (touches or boolean or small):return
        terms+=len(a)+len(b)
        if len(raw)>=MAX_ROWS or terms>MAX_TERMS:raise relation.RelationError('routing finite candidate pool bound exceeded')
        index=row['row'];raw[index]=(a,b)
        normalized[index]=tuple(canonical((0 if c==copy else c,v) for c,v in lc) for lc in (a,b))
    identity=relation.inspect(stream,expected_relation=metadata['relation_digest'],row_observer=observe)
    if identity['domain_size']!=metadata['domain_size'] or identity['stored_rows']!=metadata['full_rows']:
        raise relation.RelationError('routing original full identity/shape mismatch')
    plan,used=_plan(selected,raw,normalized)
    rows=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in raw[i][0]],b=[[c,f'{v:064x}'] for c,v in raw[i][1]]) for i in sorted(used)]
    result=dict(schema=SCHEMA,identity=identity,metadata_sha256=selected['metadata_sha256'],
                role_page_sha256=selected['role_page_sha256'],permutation_page_sha256=selected['permutation_page_sha256'],
                selected_rows=rows,plan=plan,candidate_rows=len(raw),candidate_terms=terms,
                scope='Actual precision zero/inverse/Boolean/onehot and canonical permutation255 rows only; ordering/active/tag/native/UserSem remain open')
    validate(manifest_data,role_page,permutation_page,result,accepted_roles,parameter_root)
    return result


def validate(manifest_data,role_page,permutation_page,extracted,accepted_roles,parameter_root):
    selected=boundaries(manifest_data,role_page,permutation_page,accepted_roles,parameter_root)
    if (not isinstance(extracted,dict) or set(extracted)!={'schema','identity','metadata_sha256','role_page_sha256','permutation_page_sha256','selected_rows','plan','candidate_rows','candidate_terms','scope'}
            or extracted['schema']!=SCHEMA or any(extracted[key]!=selected[key] for key in ('metadata_sha256','role_page_sha256','permutation_page_sha256'))):
        raise relation.RelationError('closed routing row derivative and both source pages required')
    raw,normalized=arithmetic.normalize_selection(extracted,selected['checked']['metadata'],selected['metadata_sha256'])
    candidates=relation.natural(extracted['candidate_rows'],MAX_ROWS+1)
    terms=relation.natural(extracted['candidate_terms'],MAX_TERMS+1)
    if candidates<len(raw) or terms<sum(len(a)+len(b) for a,b in raw.values()):
        raise relation.RelationError('routing candidate inventory below selected coverage')
    plan,used=_plan(selected,raw,normalized)
    if used!=set(raw) or json.dumps(plan,sort_keys=True,separators=(',',':'))!=json.dumps(extracted['plan'],sort_keys=True,separators=(',',':')):
        raise relation.RelationError('routing actual row plan/coverage changed')
    return selected,plan
