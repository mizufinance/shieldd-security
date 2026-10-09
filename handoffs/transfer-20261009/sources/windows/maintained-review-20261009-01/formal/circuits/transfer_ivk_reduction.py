"""Strict reduction LC ingress; raw DAG topology does not prove source semantics."""
import re
from . import transfer_relation as relation
from .transfer_balance_rows import source_index, canonical, combine
from .transfer_canonical_balance import ORDER
from .transfer_ivk_rows import SCOPE
P = relation.MODULUS
TAIL = P - 8 * ORDER


def inspect_metadata(data, ivk, expected_relation):
    if not isinstance(expected_relation,str) or not re.fullmatch('[0-9a-f]{64}',expected_relation):
        raise relation.RelationError('exact reduction relation required')
    if not isinstance(data,bytes) or len(data)>2**20:
        raise relation.RelationError('reduction metadata exceeds 1MiB')
    m=relation.record(data)
    keys={'schema','scope','relation_digest','domain_size','stored_rows','ordinary_full_ordered_rows_equal',
          'constant_copy','domain','arity','hash_handles','value','quotient','remainder','quotient_bits',
          'remainder_bits','quotient_end','remainder_end','terminal_end','equation','terminal_gate',
          'consumer','steps','expressions','nodes'}
    if set(m)!=keys or m['schema']!='shieldd-transfer-ivk-reduction-inspection-v1' or m['scope']!=SCOPE:
        raise relation.RelationError('reduction schema/scope mismatch')
    if m['relation_digest']!=expected_relation or m['ordinary_full_ordered_rows_equal'] is not True:
        raise relation.RelationError('reduction identity/noninterference mismatch')
    domain=relation.natural(m['domain_size']); count=relation.natural(m['stored_rows'])
    copy=relation.natural(m['constant_copy'],domain)
    if domain<4 or domain&(domain-1) or not 0<count<=domain or copy<3:
        raise relation.RelationError('reduction relation shape mismatch')
    if relation.natural(m['domain'],256)!=16 or relation.natural(m['arity'])!=3:
        raise relation.RelationError('reduction IVK domain mismatch')
    if any(m[k]!=ivk['metadata'][k] for k in ('domain_size','stored_rows','constant_copy','relation_digest')):
        raise relation.RelationError('reduction accepted hash shape mismatch')
    def vector(value,n):
        if not isinstance(value,list) or len(value)!=n: raise relation.RelationError('reduction vector shape')
        return [source_index(v) for v in value]
    handles=vector(m['hash_handles'],4)
    value,q,r=[source_index(m[k]) for k in ('value','quotient','remainder')]
    qb,rb=vector(m['quotient_bits'],4),vector(m['remainder_bits'],252)
    consumer=vector(m['consumer'],2)
    witnesses=[q,r,*qb,*rb,consumer[1]]
    if handles!=ivk['handles'] or value!=handles[3] or len(set(witnesses))!=len(witnesses) or any(t!=1 for t,_ in witnesses):
        raise relation.RelationError('reduction root/bit identity mismatch')
    if len(set([*handles,*witnesses,consumer[0]]))!=len(handles)+len(witnesses)+1:
        raise relation.RelationError('reduction source alias')
    expressions={}; previous=(-1,-1)
    if not isinstance(m['expressions'],list) or not 1<=len(m['expressions'])<=4096:
        raise relation.RelationError('reduction expression bound')
    for e in m['expressions']:
        if not isinstance(e,dict) or set(e)!={'source','terms'}: raise relation.RelationError('reduction expression shape')
        source=source_index(e['source'])
        if source<=previous: raise relation.RelationError('reduction expression ordering')
        previous=source; relation.terms(e['terms'],domain)
        lc=tuple((c,int(v,16)) for c,v in e['terms'])
        if any(c==copy for c,_ in lc) or source[0]==0 and any(c!=0 for c,_ in lc):
            raise relation.RelationError('reduction expression role mismatch')
        if source[0]==1 and lc!=((3+source[1],1),): raise relation.RelationError('reduction witness column mismatch')
        expressions[source]=lc
    selected={value,q,r,*qb,*rb,*consumer,source_index(m['equation']),source_index(m['terminal_gate'])}
    def observed(v):
        if not isinstance(v,dict) or len(v)!=1: raise relation.RelationError('reduction observation tag')
        if 'source' in v:
            s=source_index(v['source']); selected.add(s)
            if s not in expressions: raise relation.RelationError('missing reduction expression')
            return expressions[s]
        if 'native' in v:
            n=v['native']
            if not isinstance(n,str) or not re.fullmatch('[0-9a-f]{64}',n) or int(n,16)>=P:
                raise relation.RelationError('reduction native encoding')
            return canonical([(0,int(n,16))])
        raise relation.RelationError('unknown reduction observation')
    if not selected<=set(expressions): raise relation.RelationError('missing reduction root expression')
    if expressions[value]!=ivk['observed'][value]: raise relation.RelationError('reduction hash output LC mismatch')
    if expressions[source_index(m['equation'])]!=combine(canonical([(c,v*ORDER) for c,v in expressions[q]]),expressions[r]):
        raise relation.RelationError('reduction integer equation LC mismatch')
    folded=canonical([(3+b[1],2**i) for i,b in enumerate(rb)])
    if expressions[consumer[0]]!=folded: raise relation.RelationError('reduction consumer bit fold mismatch')
    if not isinstance(m['steps'],list) or len(m['steps'])!=3: raise relation.RelationError('reduction comparator phases')
    products=[]
    for phase,(bits,bound,end) in enumerate(zip((qb,rb,rb),(8,ORDER-1,TAIL-1),('quotient_end','remainder_end','terminal_end'))):
        steps=m['steps'][phase]
        if not isinstance(steps,list) or len(steps)!=len(bits): raise relation.RelationError('reduction step count')
        previous={'native':f'{1:064x}'}
        for i,step in enumerate(steps):
            if not isinstance(step,list) or len(step)!=6: raise relation.RelationError('reduction step shape')
            before,left,right,factor,product,after=step
            flag=(bound>>i)&1
            if before!=previous or left!={'source':list(bits[i])} or right!={'native':f'{flag:064x}'}:
                raise relation.RelationError('reduction comparator adjacency/bound mismatch')
            a,b,f,z,t=map(observed,(before,left,factor,product,after))
            expected=b if flag else combine([(0,1)],b,-1)
            target=combine(combine(z,[(0,1)]),b,-1) if flag else z
            if f!=expected or t!=target: raise relation.RelationError('reduction recurrence LC mismatch')
            if a==((0,1),):
                if z!=f: raise relation.RelationError('reduction folded first product mismatch')
            else: products.append((phase,i,a,f,z))
            previous=after
        if previous!=m[end]: raise relation.RelationError('reduction comparator endpoint mismatch')
        observed(m[end])
    if selected!=set(expressions): raise relation.RelationError('extra reduction expression')
    nodes={}; last=-1
    if not isinstance(m['nodes'],list) or len(m['nodes'])>16384: raise relation.RelationError('reduction node bound')
    for node in m['nodes']:
        if not isinstance(node,dict) or set(node)!={'index','multiply','left','right'} or type(node['multiply']) is not bool:
            raise relation.RelationError('reduction node shape')
        i=relation.natural(node['index'],2**32)
        if i<=last: raise relation.RelationError('reduction node ordering')
        last=i; children=[source_index(node[k]) for k in ('left','right')]
        if any(t==2 and c>=i for t,c in children): raise relation.RelationError('reduction forward node edge')
        nodes[(2,i)]=children
    roots={value,q,r,*qb,*rb,consumer[1]}; pending=list(selected); reached=set()
    while pending:
        s=pending.pop()
        if s in reached or s in roots or s[0]==0: continue
        if s not in nodes: raise relation.RelationError('reduction unknown DAG boundary')
        reached.add(s); pending.extend(nodes[s])
    if reached!=set(nodes): raise relation.RelationError('reduction extra DAG nodes')
    return {'metadata':m,'expressions':expressions,'products':products,
            'scope':'comparison LC recurrence and topology checks only; actual rows, gate/inverse and source interpretation remain open'}


def extract(data, ivk, stream, expected_relation):
    """Locate finite ordinary-row templates; no kernel/source promotion."""
    import hashlib
    checked=inspect_metadata(data,ivk,expected_relation)
    m,e=checked['metadata'],checked['expressions']; copy=m['constant_copy']
    def lc(k): return e[source_index(m[k])]
    def outline(a): return canonical([(copy if c==0 else c,v) for c,v in a])
    required={}; products=[]
    def require(role,a,b=()): required.setdefault((outline(a),outline(b)),[]).append(role)
    required[(canonical([(0,1),(copy,P-1)]),())]=['constant-copy']
    for name,n in [('quotient',4),('remainder',252)]:
        bits=[source_index(b) for b in m[name+'_bits']]
        for i,b in enumerate(bits): require(f'{name}.boolean.{i}',e[b],e[b])
        require(name+'.reconstruction',combine(canonical([(3+b[1],2**i) for i,b in enumerate(bits)]),lc(name),-1))
    def obs(v): return e[source_index(v['source'])] if 'source' in v else canonical([(0,int(v['native'],16))])
    for name in ('quotient_end','remainder_end'):
        require(name+'.assertion',combine(obs(m[name]),[(0,1)],-1))
    require('hash-equation',combine(lc('equation'),lc('value'),-1))
    require('terminal-gate',lc('terminal_gate'))
    for phase,i,a,b,z in checked['products']:
        products.append((f'comparison.{phase}.{i}',outline(combine(a,b,-1)),outline(combine(a,b)),outline(z)))
    qtop=e[source_index(m['quotient_bits'][3])]
    products.append(('terminal-gate.product',outline(combine(qtop,combine([(0,1)],obs(m['terminal_end']),-1),-1)),
                     outline(combine(qtop,combine([(0,1)],obs(m['terminal_end']),-1))),outline(lc('terminal_gate'))))
    rem=e[source_index(m['consumer'][0])]; inv=e[source_index(m['consumer'][1])]
    # Var::inv creates inverse * consumer in this exact order.
    products.append(('consumer.inverse',outline(combine(inv,rem,-1)),outline(combine(inv,rem)),None))
    targets={a for _,minus,plus,_ in products for a in (minus,canonical([(c,-v) for c,v in minus]),plus)}
    matched={}; candidates={}; rows={}; assertions={}
    def observe(row):
        a=tuple((c,int(v,16)) for c,v in row['a']); b=tuple((c,int(v,16)) for c,v in row['b'])
        key=(a,b)
        if not b: assertions[a]=row
        if key not in required and not b: key=(canonical([(c,-v) for c,v in a]),b)
        if key in required: matched.setdefault(key,row['row']); rows[row['row']]=row
        if a in targets:
            candidates.setdefault(a,[]).append((b,row['row'])); rows[row['row']]=row
            if len(candidates[a])>256: raise relation.RelationError('reduction product candidate bound')
    identity=relation.inspect(stream,expected_relation=expected_relation,row_observer=observe)
    if identity['domain_size']!=m['domain_size'] or identity['stored_rows']!=m['stored_rows']:
        raise relation.RelationError('reduction ordinary shape mismatch')
    if set(required)-set(matched): raise relation.RelationError('missing reduction actual template '+required[next(iter(set(required)-set(matched)))][0])
    pairs=[]
    for role,minus,plus,out in products:
        if out is None:
            found=None
            for aux,x in candidates.get(minus,[])+candidates.get(canonical([(c,-v) for c,v in minus]),[]):
                for b,y in candidates.get(plus,[]):
                    output=canonical([(c,v*pow(4,-1,P)) for c,v in combine(b,aux,-1)])
                    eq=combine(output,outline([(0,1)]),-1)
                    assertion=assertions.get(eq) or assertions.get(canonical([(c,-v) for c,v in eq]))
                    if assertion is not None:
                        rows[assertion['row']]=assertion
                        found=(x,y,assertion['row'])
                        break
                if found is not None: break
            if found is None: raise relation.RelationError('missing reduction materialized inverse/assertion')
            pairs.append({'role':role,'rows':list(found)})
            continue
        pair=next(((x,y) for aux,x in (candidates.get(minus,[])+candidates.get(canonical([(c,-v) for c,v in minus]),[])) for b,y in candidates.get(plus,[]) if b==combine(aux,out,4)),None)
        if pair is None: raise relation.RelationError('missing reduction actual product '+role)
        pairs.append({'role':role,'rows':list(pair)})
    indices=set(matched.values())|{i for pair in pairs for i in pair['rows']}
    return {'identity':identity,'metadata_sha256':hashlib.sha256(data).hexdigest(),
            'templates':[{'roles':roles,'row':matched[key]} for key,roles in required.items()],
            'products':pairs,'selected_rows':[rows[i] for i in sorted(indices)],
            'scope':'actual reduction row template extraction only; arbitrary-assignment kernel and source joins remain open'}


def ingress_controls(data, ivk, expected_relation):
    """Structural rejection controls; these are not semantic omission proofs."""
    import copy
    import json
    inspect_metadata(data,ivk,expected_relation)
    original=relation.record(data)
    controls=[]
    expected={'quotient-bit-alias':'reduction root/bit identity mismatch',
              'remainder-bit-order':'reduction consumer bit fold mismatch',
              'wrong-quotient-maximum':'reduction comparator adjacency/bound mismatch',
              'wrong-terminal-maximum':'reduction comparator adjacency/bound mismatch',
              'consumer-source-substitution':'reduction source alias',
              'hash-role-substitution':'reduction root/bit identity mismatch',
              'bool-domain-alias':'noncanonical unsigned integer',
              'extra-source-node':'reduction extra DAG nodes'}
    def control(name,change):
        m=copy.deepcopy(original); change(m)
        try: inspect_metadata((json.dumps(m)+'\n').encode(),ivk,expected_relation)
        except relation.RelationError as error:
            if str(error)!=expected[name]: raise relation.RelationError('wrong ingress rejection cause: '+name+': '+str(error))
            controls.append({'name':name,'rejected':True,'reason':str(error)})
        else: raise relation.RelationError('intended reduction ingress rejection absent: '+name)
    control('quotient-bit-alias',lambda m:m['quotient_bits'].__setitem__(1,m['quotient_bits'][0]))
    control('remainder-bit-order',lambda m:m['remainder_bits'].reverse())
    control('wrong-quotient-maximum',lambda m:m['steps'][0][0].__setitem__(2,{'native':f'{1:064x}'}))
    control('wrong-terminal-maximum',lambda m:m['steps'][2][0].__setitem__(2,{'native':f'{1:064x}'}))
    control('consumer-source-substitution',lambda m:m['consumer'].__setitem__(0,m['value']))
    control('hash-role-substitution',lambda m:m.__setitem__('value',m['quotient']))
    control('bool-domain-alias',lambda m:m.__setitem__('domain',True))
    control('extra-source-node',lambda m:m['nodes'].append({'index':2**32-1,'multiply':False,'left':m['quotient'],'right':m['remainder']}))
    return {'scope':'strict reduction metadata framing/template controls only; not semantic controls','controls':controls}


def scoped_controls(data, ivk, checked, expected_relation):
    """Finite assignments to selected rows only; no full Transfer witness claim."""
    import hashlib
    state=inspect_metadata(data,ivk,expected_relation)
    if checked['metadata_sha256']!=hashlib.sha256(data).hexdigest(): raise relation.RelationError('reduction control identity')
    m,e=state['metadata'],state['expressions']
    rows={r['row']:r for r in checked['selected_rows']}
    roles={role:t['row'] for t in checked['templates'] for role in t['roles']}
    pairs={x['role']:x['rows'] for x in checked['products']}
    def obs(v): return e[source_index(v['source'])] if 'source' in v else canonical([(0,int(v['native'],16))])
    def eval(lc,rho): return sum(v*rho.get(c,0) for c,v in lc)%P
    def decode(lc): return [(c,int(v,16)) for c,v in lc]
    def solve(lc,target,rho):
        unknown=[(c,v) for c,v in lc if c not in rho]
        if len(unknown)>1: raise relation.RelationError('reduction control multiple unknowns')
        if unknown:
            c,v=unknown[0];rho[c]=(target-eval(lc,rho))*pow(v,-1,P)%P
        if eval(lc,rho)!=target%P: raise relation.RelationError('reduction control inconsistent LC')
    results=[]
    cases=[('positive-one',0,1,0,1,None,None),('positive-last-canonical',8,TAIL-1,8,TAIL-1,None,None),
           ('missing-quotient-end',9,1,9,1,None,'quotient_end.assertion'),
           ('missing-remainder-end',0,ORDER,0,ORDER,None,'remainder_end.assertion'),
           ('missing-terminal-gate',8,TAIL,8,TAIL,None,'terminal-gate'),
           ('missing-quotient-reconstruction',0,1,9,1,None,'quotient.reconstruction'),
           ('missing-remainder-reconstruction',0,1,0,ORDER,None,'remainder.reconstruction'),
           ('missing-hash-equation',0,1,0,1,0,'hash-equation'),
           ('missing-inverse-minus',0,0,0,0,0,'inverse-minus'),
           ('missing-inverse-plus',0,0,0,0,0,'inverse-plus'),
           ('missing-inverse-assertion',0,0,0,0,0,'inverse-assertion')]
    for name,q,r,qw,rw,hash_value,omission in cases:
        rho={0:1,m['constant_copy']:1,3+m['quotient'][1]:qw,3+m['remainder'][1]:rw}
        for value,bits in ((q,m['quotient_bits']),(r,m['remainder_bits'])):
            rho.update({3+b[1]:(value>>i)&1 for i,b in enumerate(bits)})
        # The certified hash circuit is outside this selected reduction slice.
        # Choose an arbitrary assignment to its boundary LC, preserving q/r.
        hash_lc=e[source_index(m['value'])]
        unknown=[c for c,_ in hash_lc if c not in rho]
        for c in unknown[1:]: rho[c]=0
        solve(hash_lc,qw*ORDER+rw if hash_value is None else hash_value,rho)
        rho[3+m['consumer'][1][1]]=pow(r,-1,P) if r else 0
        for phase,steps in enumerate(m['steps']):
            for i,(before,left,right,factor,product,after) in enumerate(steps):
                solve(obs(product),eval(obs(before),rho)*eval(obs(factor),rho),rho)
                if eval(obs(after),rho)!=((1-eval(obs(left),rho))*eval(obs(right),rho)+eval(obs(product),rho))%P:
                    raise relation.RelationError('reduction control recurrence mismatch')
                key=f'comparison.{phase}.{i}'
                if key in pairs:
                    row=rows[pairs[key][0]];solve(decode(row['b']),eval(decode(row['a']),rho)**2,rho)
        # Actual terminal product output and its difference-square auxiliary.
        gate=eval(e[source_index(m['quotient_bits'][3])],rho)*(1-eval(obs(m['terminal_end']),rho))
        solve(e[source_index(m['terminal_gate'])],gate,rho)
        for key in ('terminal-gate.product','consumer.inverse'):
            minus,plus=pairs[key][:2]
            if key=='consumer.inverse' and omission in ('inverse-minus','inverse-plus','inverse-assertion'):
                aux=decode(rows[minus]['b'])
                output=canonical([(c,v*pow(4,-1,P)) for c,v in combine(decode(rows[plus]['b']),aux,-1)])
                solve(output,0 if omission=='inverse-assertion' else 1,rho)
                solve(aux,P-4 if omission=='inverse-minus' else 0,rho)
                continue
            aux=decode(rows[minus]['b']);solve(aux,eval(decode(rows[minus]['a']),rho)**2,rho)
            plus_row=rows[plus]
            solve(decode(plus_row['b']),eval(decode(plus_row['a']),rho)**2,rho)
        rejected=sorted(i for i,row in rows.items() if eval(decode(row['a']),rho)**2%P!=eval(decode(row['b']),rho))
        inverse_rows=pairs['consumer.inverse']
        inverse_omissions={'inverse-minus':inverse_rows[0],'inverse-plus':inverse_rows[1],'inverse-assertion':inverse_rows[2]}
        omitted=None if omission is None else inverse_omissions[omission] if omission in inverse_omissions else roles[omission]
        if rejected!= ([] if omitted is None else [omitted]): raise relation.RelationError('intended reduction semantic omission absent')
        if omission=='quotient_end.assertion' and not rho[3+m['quotient'][1]]>8: raise relation.RelationError('quotient control predicate absent')
        if omission=='remainder_end.assertion' and not rho[3+m['remainder'][1]]>=ORDER: raise relation.RelationError('remainder control predicate absent')
        if omission=='terminal-gate' and not q*ORDER+r>=P: raise relation.RelationError('wrap control predicate absent')
        if omission=='quotient.reconstruction' and not rho[3+m['quotient'][1]]>8: raise relation.RelationError('quotient reconstruction predicate absent')
        if omission=='remainder.reconstruction' and not rho[3+m['remainder'][1]]>=ORDER: raise relation.RelationError('remainder reconstruction predicate absent')
        if omission=='hash-equation' and eval(hash_lc,rho)==(qw*ORDER+rw)%P: raise relation.RelationError('hash equation predicate absent')
        if omission in inverse_omissions and eval(e[source_index(m['consumer'][0])],rho)!=0: raise relation.RelationError('inverse nonzero predicate absent')
        results.append({'name':name,'q_bits_value':q,'r_bits_value':r,'q':qw,'r':rw,'omitted_original_row':omitted,'original_rejected_rows':rejected,'assignment':sorted(rho.items())})
    return {'scope':'selected reduction modular-field semantic controls only; full hash and Transfer constraints excluded','cases':results}
