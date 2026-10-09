"""Shared bounded matcher for original squared rows and Div materializations.

Inputs are canonical outlined operand LCs. This matches algebraic templates
against the complete replayed relation; it never substitutes a desired product
into a quotient witness or treats a digest as algebraic correspondence.
"""
from . import transfer_relation as relation
from .transfer_balance_rows import canonical, combine


def normalize_selection(extracted, metadata, metadata_hash):
    """Revalidate persisted extraction row identities and canonical terms."""
    if not isinstance(extracted,dict) or extracted.get('metadata_sha256')!=metadata_hash:
        raise relation.RelationError('arithmetic extraction metadata identity mismatch')
    identity=extracted.get('identity')
    if (not isinstance(identity,dict) or identity.get('relation_digest')!=metadata['relation_digest'] or
            relation.natural(identity.get('domain_size'))!=metadata['domain_size'] or
            relation.natural(identity.get('stored_rows'))!=metadata['full_rows']):
        raise relation.RelationError('arithmetic extraction relation identity/shape mismatch')
    records=extracted.get('selected_rows')
    if not isinstance(records,list) or not 1<=len(records)<=8192:
        raise relation.RelationError('arithmetic selected row bound')
    raw={};normalized={};previous=-1;copy=metadata['constant_copy']
    for row in records:
        if not isinstance(row,dict) or set(row)!={'row','a','b'}:
            raise relation.RelationError('arithmetic selected row closed shape')
        index=relation.natural(row['row'],metadata['full_rows'])
        if index<=previous:raise relation.RelationError('arithmetic selected rows unordered/duplicate')
        previous=index
        for key in ('a','b'):relation.terms(row[key],metadata['domain_size'])
        raw[index]=tuple(tuple((column,int(value,16)) for column,value in row[key]) for key in ('a','b'))
        normalized[index]=tuple(canonical((0 if column==copy else column,value) for column,value in lc) for lc in raw[index])
    constant=(canonical([(0,1),(copy,-1)]),())
    if constant not in raw.values():raise relation.RelationError('arithmetic constant link missing')
    return raw,normalized


def product_certificate(left,right,output,normalized):
    """Certify a captured multiplication without a desired-output premise."""
    for side,scalar,other in (('left',left,right),('right',right,left)):
        if not scalar or len(scalar)==1 and scalar[0][0]==0:
            coefficient=scalar[0][1] if scalar else 0
            if output!=canonical((c,v*coefficient) for c,v in other):
                raise relation.RelationError('arithmetic folded product mismatch')
            return dict(kind='folded_'+side,coefficient=coefficient,rows=[])
    if left==right:
        index=next((i for i,row in normalized.items() if row==(left,output)),None)
        if index is None:raise relation.RelationError('arithmetic captured square missing')
        return dict(kind='square',rows=[index])
    minus,plus=combine(left,right,-1),combine(left,right)
    for swapped,difference in ((False,minus),(True,canonical((c,-v) for c,v in minus))):
        for first,(a,auxiliary) in normalized.items():
            if a!=difference:continue
            second=next((i for i,row in normalized.items() if row==(plus,combine(auxiliary,output,4))),None)
            if second is not None:return dict(kind='product',rows=[first,second],auxiliary=auxiliary,swapped=swapped)
    raise relation.RelationError('arithmetic captured product pair missing')


def quotient_certificate(numerator,denominator,quotient,normalized):
    """Keep actual quotient*denominator materialization and numerator equality."""
    table={row:i for i,row in normalized.items()}
    def assertion(output):
        equation=combine(output,numerator,-1)
        if not equation:return []
        index=table.get((equation,()))
        if index is None:index=table.get((canonical((c,-v) for c,v in equation),()))
        if index is None:return None
        return [index]
    for scalar,other in ((denominator,quotient),(quotient,denominator)):
        if not scalar or len(scalar)==1 and scalar[0][0]==0:
            coefficient=scalar[0][1] if scalar else 0
            output=canonical((c,v*coefficient) for c,v in other); rows=assertion(output)
            if rows is None:raise relation.RelationError('arithmetic folded quotient assertion missing')
            return dict(kind='folded',coefficient=coefficient,output=output,rows=rows,
                        numerator=numerator,denominator=denominator,quotient=quotient)
    for first,(a,b) in normalized.items():
        if quotient==denominator:
            if a!=quotient:continue
            output=b;indices=[first];certificate=dict(kind='square')
            rows=assertion(output)
            if rows is not None:return dict(certificate,output=output,rows=indices+rows,
                numerator=numerator,denominator=denominator,quotient=quotient)
        else:
            minus=combine(quotient,denominator,-1);plus=combine(quotient,denominator)
            if a not in (minus,canonical((c,-v) for c,v in minus)):continue
            for second,(c,d) in normalized.items():
                if c!=plus:continue
                output=canonical((col,v*pow(4,-1,relation.MODULUS)) for col,v in combine(d,b,-1))
                rows=assertion(output)
                if rows is not None:return dict(kind='product',output=output,auxiliary=b,swapped=a!=minus,
                    rows=[first,second]+rows,numerator=numerator,denominator=denominator,quotient=quotient)
    raise relation.RelationError('arithmetic quotient materialization/assertion missing')


def completion_certificate(certificate, normalized):
    """Transport an actual generic quotient to the constructive3-write model.

    Folded, square, swapped or fused shapes outside that model return None;
    their arithmetic soundness remains covered by quotient_certificate.
    """
    if certificate['kind']!='product' or certificate.get('swapped') or len(certificate['rows'])!=3:
        return None
    q=certificate['quotient'];aux=certificate['auxiliary'];out=certificate['output']
    if len(q)!=1 or q[0][1]!=1 or len(aux)!=1 or aux[0][1]!=1:return None
    inputs=certificate['numerator']+certificate['denominator']
    occupied={c for c,_ in inputs}|{0,q[0][0],aux[0][0]}
    fresh=[c for c,v in out if v==1 and c not in occupied]
    if len(fresh)!=1:return None
    product=fresh[0];remainder=tuple((c,v) for c,v in out if c!=product)
    writes={q[0][0],product,aux[0][0]}
    if len(writes)!=3 or any(c in writes for c,_ in inputs+remainder):return None
    expected=[(combine(q,certificate['denominator'],-1),aux),
              (combine(q,certificate['denominator']),combine(aux,out,4)),
              (combine(out,certificate['numerator'],-1),())]
    if any(normalized[index]!=row for index,row in zip(certificate['rows'],expected)):return None
    return dict(quotient=q[0][0],product=product,auxiliary=aux[0][0],remainder=remainder,
                numerator=certificate['numerator'],denominator=certificate['denominator'],rows=certificate['rows'])


def product_completion_certificate(left, right, output, certificate, normalized):
    """Keep the unique fresh unit pivot of an exact actual two-row product.

    This certifies a local two-write construction. Preservation of surrounding
    rows and support ownership across successive products are separate joins.
    Folded/square products or ambiguous pivots are not promoted to this shape.
    """
    if certificate['kind'] != 'product' or len(certificate['rows']) != 2:
        return None
    auxiliary = certificate['auxiliary']
    if len(auxiliary) != 1 or auxiliary[0][1] != 1 or auxiliary[0][0] == 0:
        return None
    if certificate.get('swapped'):
        left, right = right, left
    occupied = {c for c, _ in left + right} | {0, auxiliary[0][0]}
    pivots = [c for c, v in output if v == 1 and c not in occupied]
    if len(pivots) != 1:
        return None
    pivot = pivots[0]
    remainder = tuple((c, v) for c, v in output if c != pivot)
    writes = {pivot, auxiliary[0][0]}
    if len(writes) != 2 or any(c in writes for c, _ in left + right + remainder):
        return None
    expected = [(combine(left, right, -1), auxiliary),
                (combine(left, right), combine(auxiliary, output, 4))]
    if any(normalized[index] != row for index, row in zip(certificate['rows'], expected)):
        return None
    return dict(left=left, right=right, remainder=remainder, output=pivot,
                auxiliary=auxiliary[0][0], rows=certificate['rows'])


def folded_quotient_completion_certificate(certificate, normalized):
    """Keep the real fresh unit quotient and its sole linear assertion.

    This intentionally admits only denominator one, as used for the captured
    initial identity accumulator. No product/inverse/auxiliary row is invented.
    """
    if (certificate['kind'] != 'folded' or certificate['denominator'] != ((0,1),)
            or certificate['coefficient'] != 1 or len(certificate['rows']) != 1):
        return None
    quotient=certificate['quotient'];input_lc=certificate['numerator']
    if (len(quotient)!=1 or quotient[0][1]!=1 or quotient[0][0]==0
            or any(c==quotient[0][0] for c,_ in input_lc)):
        return None
    expected=combine(quotient,input_lc,-1)
    actual=normalized[certificate['rows'][0]]
    if actual != (expected,()):return None
    return dict(input=input_lc,remainder=(),output=quotient[0][0],rows=certificate['rows'])


def extract_templates(stream, expected_relation, domain, count, required, products, squares, *, label='arithmetic'):
    """Match direct rows plus (role,minus,plus,out,numerator) obligations.

    Exactly one of out/numerator is supplied for a nonlinear product. When
    numerator is supplied, the separate materialized-output equality is kept.
    Square obligations are (role,input,numerator) and also retain the assertion.
    """
    p=relation.MODULUS
    targets={a for _,minus,plus,_,_ in products for a in
             (minus,canonical((c,-v) for c,v in minus),plus)}
    targets.update(a for _,a,_ in squares)
    matched,candidates,assertions,rows = {},{},{},{}
    def observe(row):
        a=tuple((c,int(v,16)) for c,v in row['a']); b=tuple((c,int(v,16)) for c,v in row['b'])
        if not b: assertions.setdefault(a,row)
        key=(a,b)
        if key not in required:key=(canonical((c,-v) for c,v in a),b)
        if key in required:matched.setdefault(key,row['row']);rows[row['row']]=row
        if a in targets:
            candidates.setdefault(a,[]).append((b,row['row']));rows[row['row']]=row
            if len(candidates[a])>256:raise relation.RelationError(label+' product candidate bound')
    identity=relation.inspect(stream,expected_relation=expected_relation,row_observer=observe)
    if identity['domain_size']!=domain or identity['stored_rows']!=count:
        raise relation.RelationError(label+' ordinary shape mismatch')
    missing=set(required)-set(matched)
    if missing:raise relation.RelationError('missing '+label+' actual template '+required[next(iter(missing))][0])
    pairs=[]
    for role,minus,plus,out,numerator in products:
        found=None
        for auxiliary,x in candidates.get(minus,[])+candidates.get(canonical((c,-v) for c,v in minus),[]):
            for b,y in candidates.get(plus,[]):
                output=canonical((c,v*pow(4,-1,p)) for c,v in combine(b,auxiliary,-1))
                if out is not None and output==out:found=(x,y);break
                if numerator is not None:
                    equation=combine(output,numerator,-1)
                    assertion=assertions.get(equation) or assertions.get(canonical((c,-v) for c,v in equation))
                    if assertion is not None:rows[assertion['row']]=assertion;found=(x,y,assertion['row']);break
            if found is not None:break
        if found is None:raise relation.RelationError('missing '+label+' materialized product/assertion '+role)
        pairs.append({'role':role,'rows':list(found)})
    for role,input_lc,numerator in squares:
        found=None
        for output,index in candidates.get(input_lc,[]):
            equation=combine(output,numerator,-1)
            assertion=assertions.get(equation) or assertions.get(canonical((c,-v) for c,v in equation))
            if assertion is not None:
                rows[assertion['row']]=assertion;found=(index,assertion['row']);break
        if found is None:raise relation.RelationError('missing '+label+' materialized square/assertion '+role)
        pairs.append({'role':role,'rows':list(found)})
    indices=set(matched.values())|{i for pair in pairs for i in pair['rows']}
    return dict(identity=identity,templates=[{'roles':roles,'row':matched[key]} for key,roles in required.items()],
                products=pairs,selected_rows=[rows[i] for i in sorted(indices)])


def infer_product_outputs(stream, expected_relation, domain, count, operands, copy, *, require_unit_output=False):
    """Infer unique materialized LCs from actual rows with known input LCs.

    No source handle is created. An inferred LC is justified only by its exact
    row pair (or square/fold), and remains subject to downstream row joins.
    """
    if not isinstance(operands,dict) or not 1<=len(operands)<=4:
        raise relation.RelationError('inferred product operand bound')
    outlined=lambda lc:canonical((copy if c==0 else c,v) for c,v in lc)
    targets=set();result={};pending={}
    for role,(left,right) in operands.items():
        folded=next(((scalar,other) for scalar,other in ((left,right),(right,left))
                     if not scalar or len(scalar)==1 and scalar[0][0]==0),None)
        if folded:
            scalar,other=folded;coefficient=scalar[0][1] if scalar else 0
            result[role]=dict(output=canonical((c,v*coefficient) for c,v in other),rows=[])
        elif left==right:
            pending[role]=('square',outlined(left));targets.add(outlined(left))
        else:
            minus,plus=outlined(combine(left,right,-1)),outlined(combine(left,right))
            pending[role]=('product',minus,plus)
            targets.update((minus,canonical((c,-v) for c,v in minus),plus))
    candidates={};rows={}
    def observe(row):
        a,b=(tuple((c,int(v,16)) for c,v in row[key]) for key in ('a','b'))
        if a not in targets:return
        candidates.setdefault(a,[]).append((b,row['row']));rows[row['row']]=row
        if len(candidates[a])>256:raise relation.RelationError('inferred product candidate bound')
    identity=relation.inspect(stream,expected_relation=expected_relation,row_observer=observe)
    if identity['domain_size']!=domain or identity['stored_rows']!=count:
        raise relation.RelationError('inferred product ordinary shape mismatch')
    unoutline=lambda lc:canonical((0 if c==copy else c,v) for c,v in lc)
    for role,request in pending.items():
        if request[0]=='square':matches=[(unoutline(out),(index,)) for out,index in candidates.get(request[1],[])]
        else:
            _,minus,plus=request
            matches=[(unoutline(canonical((c,v*pow(4,-1,relation.MODULUS)) for c,v in combine(b,aux,-1))),(x,y))
                     for aux,x in candidates.get(minus,[])+candidates.get(canonical((c,-v) for c,v in minus),[])
                     for b,y in candidates.get(plus,[]) if x!=y]
        matches=list(dict.fromkeys(matches))
        if require_unit_output:
            # A source-specific caller may require a materialized single-column
            # result. This rejects cross-joins against unrelated rows sharing a
            # constant sum; it never selects among two valid materializations.
            matches=[item for item in matches if len(item[0])==1 and item[0][0][0]!=0 and item[0][0][1]==1]
        if len(matches)!=1:raise relation.RelationError('inferred product must have one exact actual match: '+role)
        output,indices=matches[0];result[role]=dict(output=output,rows=list(indices))
    selected={i for item in result.values() for i in item['rows']}
    return dict(identity=identity,products=result,selected_rows=[rows[i] for i in sorted(selected)])
