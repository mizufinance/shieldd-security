"""Five typed folded source pages and real small digest stream; no runtime credit."""
import copy,hashlib,io
import unittest
from unittest.mock import patch
from blake3 import blake3
from circuits import transfer_balance_variable as variable,transfer_balance_variable_batch as batch
from circuits import transfer_ownership as ownership,transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_epk_fixed import encoded


def fixture():
    p=relation.MODULUS;bits=[(1,10+i) for i in range(129)]
    I=(('native',0),('native',1));nodes={};derived={h:((h[1]+3,1),) for h in bits+[(1,500),(1,501)]}
    constants={};next_node=1000;windows=[];quotients=[]
    def formula(kind,axis,inputs):
        nonlocal next_node
        graph,roles=ownership.expected_formula(kind,axis,inputs)
        if not graph['arity']:
            assert graph['nodes'][graph['output']]['kind']=='constant'
            return ('native',graph['nodes'][graph['output']]['value'])
        handles=[]
        for node in graph['nodes']:
            if node['kind']=='input':handle=roles[node['slot']]
            elif node['kind']=='constant':
                value=node['value']
                if value not in constants:
                    constants[value]=(0,len(constants));derived[constants[value]]=canonical([(0,value)])
                handle=constants[value]
            else:
                left,right=handles[node['left']],handles[node['right']]
                handle=(2,next_node);next_node+=1;multiply=node['kind']=='mul';nodes[handle]=(multiply,left,right)
                a,b=derived[left],derived[right]
                if not multiply:derived[handle]=combine(a,b)
                else:
                    folded=next((lc,other) for lc,other in ((a,b),(b,a)) if all(c==0 for c,_ in lc))
                    lc,other=folded;factor=lc[0][1] if lc else 0;derived[handle]=canonical((c,v*factor) for c,v in other)
            handles.append(handle)
        return ('source',handles[graph['output']])
    def quotient(kind,inputs,output):
        return tuple(formula(kind+'.'+part,axis,inputs) for part in ('numerator','denominator') for axis in ('x','y'))+output
    precompute=[quotient('double',I,I),quotient('add',I+I,I)]
    for index in range(65):
        low=128-2*index;pair=(('source',bits[low]),('native',0) if not index else ('source',bits[low+1]))
        selected=tuple(formula('select',axis,I+I+I+pair) for axis in ('x','y'))
        q=[quotient('double',I,I),quotient('double',I,I),quotient('add',I+selected,I)]
        windows.append((I,I,I,selected,I));quotients.append(q)
    def ref(value):return {'source':list(value[1])} if value[0]=='source' else {'native':f'{value[1]:064x}'}
    point=lambda values:list(map(ref,values))
    rows=[dict(row=0,a=[[0,f'{1:064x}'],[16000,f'{p-1:064x}']],b=[])]
    for _,index in bits:
        terms=[[index+3,f'{1:064x}']];rows.append(dict(row=len(rows),a=terms,b=terms))
    header=dict(schema='shieldd-transfer-relation-v1',family='transfer',relation_digest='',domain_size=16384,stored_rows=len(rows),
        public_inputs=1,committed_blocks=[1],constant_column=0,public_columns=[1],committed_columns=[[2]],
        source_public=[[1,500]],source_blocks=[[[1,501]]],coefficient_encoding='canonical-big-endian-32',field_modulus=str(p),
        role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',padding='implicit-all-zero-rows-to-domain-size')
    h=blake3();h.update(relation.NAMESPACE+relation.u64(16384)+relation.u64(len(rows))+
        relation.indices(header['source_public'])+relation.u64(1)+relation.indices(header['source_blocks'][0]))
    for row in rows:h.update(b'A'+relation.terms(row['a'],16384)+b'B'+relation.terms(row['b'],16384))
    digest=h.hexdigest();header['relation_digest']=digest
    signed=dict(identity=dict(relation_digest=digest),copy=16000,negative=503,magnitude=504,bits=[i+3 for _,i in bits],metadata_sha256='b'*64)
    common=dict(schema='shieldd-transfer-balance-variable-v1',family='transfer',scope=variable.SCOPE,
        relation_digest=digest,domain_size=16384,full_rows=len(rows),constant_copy=16000,
        ordinary_full_ordered_rows_equal=False,repeated_observations_equal=False,total_windows=65,bit_width=129,
        negative={'source':[1,500]},magnitude={'source':[1,501]},base=point(I),twice=point(I),triple=point(I),
        output=point(I),bits=[list(bit) for bit in bits],precompute_quotients=[point(q) for q in precompute])
    pages=[];descriptors=[]
    for ordinal in range(5):
        start=16*ordinal;count=min(16,65-start);local=[];roots=set(bits)|{(1,500),(1,501)}
        for index in range(start,start+count):
            low=128-2*index;pair=(('source',bits[low]),('native',0) if not index else ('source',bits[low+1]))
            local.append(dict(index=index,points=[point(v) for v in windows[index]],bits=list(map(ref,pair)),quotients=[point(q) for q in quotients[index]]))
            for values in [*windows[index],*quotients[index]]:roots.update(v[1] for v in values if v[0]=='source')
        pending=list(roots);visited=set();required=set(roots)
        while pending:
            source=pending.pop()
            if source in visited:continue
            visited.add(source)
            if source[0]==2:
                m,left,right=nodes[source]
                if m and left[0]!=0 and right[0]!=0:required.update((source,left,right))
                pending.extend((left,right))
            else:required.add(source)
        obj=dict(common,window_start=start,window_count=count,windows=local,
            expressions=[dict(source=list(s),terms=[[c,f'{v:064x}'] for c,v in derived[s]]) for s in sorted(required)],
            nodes=[dict(index=s[1],multiply=m,left=list(l),right=list(r)) for s,(m,l,r) in sorted(nodes.items()) if s in visited])
        data=encoded(obj);pages.append(data);descriptors.append(dict(ordinal=ordinal,window_start=start,window_count=count,blake3=blake3(data).hexdigest()))
    parent={key:common[key] for key in ('family','relation_digest','domain_size','full_rows','constant_copy')}
    parent.update(schema='shieldd-transfer-balance-variable-pages-v1',scope='5 bounded balance129 window pages from one lowering; group/native joins open',
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,pages=descriptors)
    stream=b''.join(encoded(row) for row in [header,*rows,dict(eof=True,rows=len(rows))])
    return encoded(parent),pages,digest,signed,point(I),stream


class BalanceBatchTests(unittest.TestCase):
    def test_real_small_stream_one_replay_and_complete_five_typed_projections(self):
        parent,pages,digest,signed,base,data=fixture()
        with patch.object(batch.arithmetic,'extract_templates',wraps=batch.arithmetic.extract_templates) as matcher:
            extracted=batch.extract_rows(parent,pages,digest,signed,base,io.BytesIO(data),include_bits=True)
            matcher.assert_called_once()
        checked=variable.inspect_pages(parent,pages,digest,signed,base)
        self.assertEqual(extracted['identity']['raw_sha256'],hashlib.sha256(data).hexdigest())
        self.assertEqual(len(extracted['selected_rows']),130)
        self.assertEqual([len(page['rows']) for page in extracted['pages']],[32,33,33,33,3])
        for ordinal in range(5):
            selected=batch.page_selection(checked,extracted,ordinal)
            self.assertFalse(checked['chunks'][ordinal]['metadata']['ordinary_full_ordered_rows_equal'])
            self.assertEqual(selected['signed_parent_metadata_sha256'],'b'*64)
        for bit in (0,1):
            rho=lambda c:1 if c in (0,16000) else bit
            for row in extracted['selected_rows']:
                a,b=(sum(rho(c)*int(v,16) for c,v in row[side])%relation.MODULUS for side in ('a','b'))
                self.assertEqual(a*a%relation.MODULUS,b)

    def test_typed_parent_original_and_persisted_mutations_refuse(self):
        parent,pages,digest,signed,base,data=fixture()
        extracted=batch.extract_rows(parent,pages,digest,signed,base,io.BytesIO(data),include_bits=True)
        checked=variable.inspect_pages(parent,pages,digest,signed,base)
        for edit in ('parent','row','missing','descriptor','bitflag'):
            changed=copy.deepcopy(extracted)
            if edit=='parent':changed['parent_sha256']='f'*64
            elif edit=='row':changed['selected_rows'][1]['b']=[]
            elif edit=='missing':changed['selected_rows'].pop()
            elif edit=='descriptor':changed['pages'][4]['window_start']=63
            else:changed['include_bits']=1
            with self.subTest(edit=edit),self.assertRaises(relation.RelationError):batch.page_selection(checked,changed,4 if edit in ('row','descriptor') else 0)
        bad=relation.record(parent);bad['pages'][1]['ordinal']=2
        with self.assertRaises(relation.RelationError):batch.extract_rows(encoded(bad),pages,digest,signed,base,io.BytesIO(data))
        for changed in (data[:-1],data+b'x'):
            with self.assertRaises(relation.RelationError):batch.extract_rows(parent,pages,digest,signed,base,io.BytesIO(changed))


if __name__=='__main__':unittest.main()
