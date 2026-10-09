"""Synthetic ownership arithmetic fixture; never runtime or digest evidence."""

def symbolic_window():
    from pathlib import Path
    from circuits import transfer_ownership as o
    P=o.relation.MODULUS
    native=lambda v:('native',v)
    w=lambda i:('source',(1,i))
    points={name:(w(2*i),w(2*i+1)) for i,name in enumerate(('base','twice','triple','input','first','second','result'))}
    derived={(1,i):((3+i,1),) for i in list(range(14))+list(range(100,352))}
    nodes={};expressions=dict(derived);rows=[(o.canonical([(0,1),(16000,-1)]),())]
    next_id=1000;next_column=4000;next_constant=0
    constants={}
    def emit(a,b=()):
     rows.append(tuple(o.canonical((16000 if c==0 else c,v) for c,v in terms) for terms in (a,b)))
    def multiplication(a,b):
     nonlocal next_column
     folded=next(((lc,other) for lc,other in ((a,b),(b,a)) if not lc or len(lc)==1 and lc[0][0]==0),None)
     if folded:
      lc,other=folded;v=lc[0][1] if lc else 0
      return o.canonical((c,k*v) for c,k in other)
     output=((next_column,1),);next_column+=1
     if a==b:emit(a,output)
     else:
      aux=((next_column,1),);next_column+=1
      emit(o.combine(a,b,-1),aux);emit(o.combine(a,b),o.combine(aux,output,4))
     return output
    def formula(kind,axis,inputs):
     nonlocal next_id,next_constant
     graph,roles=o.expected_formula(kind,axis,inputs);handles=[]
     for node in graph['nodes']:
      if node['kind']=='input':handle=roles[node['slot']]
      elif node['kind']=='constant':
       value=node['value']
       if value not in constants:
        constants[value]=(0,next_constant);next_constant+=1
        derived[constants[value]]=o.canonical([(0,value)])
        expressions[constants[value]]=derived[constants[value]]
       handle=constants[value]
      else:
       left,right=handles[node['left']],handles[node['right']]
       handle=(2,next_id);next_id+=1
       multiply=node['kind']=='mul';nodes[handle]=(multiply,left,right)
       derived[handle]=multiplication(derived[left],derived[right]) if multiply else o.combine(derived[left],derived[right])
       expressions[handle]=derived[handle]
      handles.append(handle)
     return ('source',handles[graph['output']])
    bits=[(1,100+i) for i in range(252)]
    selector_inputs=points['base']+points['twice']+points['triple']+(('source',bits[248]),('source',bits[249]))
    points['selected']=tuple(formula('select',axis,selector_inputs) for axis in ('x','y'))
    quotients=[]
    def quotient(kind,inputs,output):
     values=tuple(formula(kind+'.'+part,axis,inputs) for part in ('numerator','denominator') for axis in ('x','y'))+output
     for axis in range(2):
      numerator,denominator,q=(derived[v[1]] for v in (values[axis],values[axis+2],values[axis+4]))
      product=multiplication(q,denominator)
      emit(o.combine(product,numerator,-1))
     quotients.append(values)
    quotient('double',points['base'],points['twice'])
    quotient('add',points['twice']+points['base'],points['triple'])
    quotient('double',points['input'],points['first'])
    quotient('double',points['first'],points['second'])
    quotient('add',points['second']+points['selected'],points['result'])
    metadata={'relation_digest':'a'*64,'constant_copy':16000,'domain_size':16384,'full_rows':len(rows),'window_start':1,'window_count':1}
    c={'metadata':metadata,'points':{**points,'output':points['result'],'target':points['result']},'windows':[(points['input'],points['first'],points['second'],points['selected'],points['result'])],'bits':bits,'derived':derived,'expressions':expressions,'nodes':nodes,'quotients':quotients}
    encoded=[{'row':i,'a':[[col,f'{v:064x}'] for col,v in a],'b':[[col,f'{v:064x}'] for col,v in b]} for i,(a,b) in enumerate(rows)]
    # The stream checker is isolated here: these are synthetic original rows, not a
    # runtime relation or a digest-qualified capture. Formula matching is real.
    from unittest.mock import patch
    def inspect(stream,expected_relation,row_observer):
     for row in encoded:row_observer(row)
     return {'relation_digest':'a'*64,'domain_size':16384,'stored_rows':len(rows)}
    with patch.object(o.relation,'inspect',side_effect=inspect):e=o.extract_rows(c,None,'a'*64)
    return c,e
