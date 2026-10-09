"""Synthetic complete48source wiring and actual row tests; no runtime qualification."""
import copy,io,json,unittest
from pathlib import Path
from blake3 import blake3
from circuits import transfer_note_tree as tree,transfer_note_t4_pages as pages
from circuits import transfer_note_hash as hashes,transfer_note_hash_pages as hash_pages,transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from integration import note_tree_observer as hooks,note_hash_observer as hash_hooks,note_spend_observer as spend_hooks
from tests.test_transfer_note_spend import fixture,encoded,source


def tree_fixture(rows_override=None):
    data,_,caller=fixture();note=json.loads(data)
    note.update(domain_size=4096,constant_copy=4000)
    caller['metadata'].update(domain_size=4096,constant_copy=4000)
    observed={tuple(e['source']):tuple((c,int(v,16)) for c,v in e['terms']) for e in note['expressions']}
    def get(ref):return observed[tuple(ref['source'])]
    def put(tag,index,lc=None):
        ref=source(tag,index);observed[(tag,index)]=canonical([(3+index,1)] if lc is None else lc);return ref
    levels=[];rows=[(canonical([(0,1),(4000,-1)]),())]
    for ordinal in range(48):
        slot,index=divmod(ordinal,24);spend=note['spends'][slot]
        node=spend['commitment'] if index==0 else levels[-1]['output']
        low,high=[{'source':b} for b in spend['position_bits'][2*index:2*index+2]]
        siblings=[put(1,1200+3*ordinal+j) for j in range(3)]
        products=[]
        def product(bit,delta,j):
            right=put(2,10000+32*ordinal+2*j,delta)
            out=put(2,10001+32*ordinal+2*j,[(2500+6*ordinal+j,1)])
            products.append([bit,right,out]);return out
        first,second,third=map(get,siblings);node_lc=get(node)
        ls=product(low,combine(first,node_lc,-1),0)
        rs=product(low,combine(third,node_lc,-1),1)
        bases=[combine(node_lc,get(ls)),combine(first,get(ls),-1),second,third]
        deltas=[combine(first,bases[0],-1),combine(second,bases[1],-1),
                combine(combine(node_lc,get(rs)),second,-1),combine(combine(third,get(rs),-1),third,-1)]
        outputs=[product(high,delta,j+2) for j,delta in enumerate(deltas)]
        children=[put(2,10020+32*ordinal+j,combine(base,get(out))) for j,(base,out) in enumerate(zip(bases,outputs))]
        output=spend['computed_anchor'] if index==23 else put(2,20000+ordinal,[(3400+ordinal,1)])
        levels.append(dict(slot=slot,level=index,node=node,low=low,high=high,siblings=siblings,
                           swaps=[ls,rs],children=children,output=output,products=products))
        rows.extend((get(bit),get(bit)) for bit in (low,high))
        for j,p in enumerate(products):
            a,b,z=map(get,p);aux=((3100+6*ordinal+j,1),)
            rows.extend([(combine(a,b,-1),aux),(combine(a,b),combine(aux,z,4))])
    if rows_override is not None:rows=rows_override
    outline=lambda lc:canonical((4000 if c==0 else c,v) for c,v in lc)
    records=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in (a if i==0 else outline(a))],
                  b=[[c,f'{v:064x}'] for c,v in (b if i==0 else outline(b))]) for i,(a,b) in enumerate(rows)]
    digest=blake3();public=[[1,990]];blocks=[[1,991]]
    digest.update(relation.NAMESPACE+relation.u64(4096)+relation.u64(len(rows))+
                  relation.indices(public)+relation.u64(1)+relation.indices(blocks))
    for row in records:digest.update(b'A'+relation.terms(row['a'],4096)+b'B'+relation.terms(row['b'],4096))
    identity=dict(relation_digest=digest.hexdigest(),full_rows=len(rows))
    note.update(identity);caller['metadata'].update(identity)
    obj=dict(schema='shieldd-transfer-note-tree-v1',family='transfer',scope=tree.SCOPE,
        **{k:note[k] for k in ('relation_digest','domain_size','full_rows','constant_copy')},
        ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,domain=1,depth=24,levels=levels,
        expressions=[dict(source=list(h),terms=[[c,f'{v:064x}'] for c,v in lc]) for h,lc in sorted(observed.items())],spend=note)
    header=dict(schema='shieldd-transfer-relation-v1',family='transfer',relation_digest=digest.hexdigest(),
        domain_size=4096,stored_rows=len(rows),public_inputs=1,committed_blocks=[1],constant_column=0,
        public_columns=[1],committed_columns=[[2]],source_public=public,source_blocks=[blocks],
        coefficient_encoding='canonical-big-endian-32',field_modulus=str(relation.MODULUS),
        role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',
        padding='implicit-all-zero-rows-to-domain-size')
    stream=io.BytesIO(b''.join(encoded(v) for v in [header,*records,dict(eof=True,rows=len(rows))]))
    return obj,encoded(note),caller,stream,rows


def state_page(obj,ordinal):
    level=obj['levels'][ordinal];slot,index=divmod(ordinal,24)
    observed={tuple(e['source']):e['terms'] for e in obj['expressions']}
    def put(index,lc):
        ref=source(2,index);observed[(2,index)]=[[c,f'{v:064x}'] for c,v in lc];return ref
    prefix={'native':f'{index+1:064x}'};inputs=[prefix,*level['children']]
    before=[{'native':f'{1281:064x}'},prefix,*level['children']]
    after=[put(30000+ordinal*6+j,[(3800+j,1)]) for j in range(6)]
    after[1]=level['output']
    return dict(schema='shieldd-transfer-note-hash-block-v1',family='transfer',scope=hashes.SCOPE,
        **{k:obj[k] for k in ('relation_digest','domain_size','full_rows','constant_copy')},
        ordinary_full_ordered_rows_equal=False,repeated_observations_equal=False,slot=slot,role='state',level=index,block=0,
        hash=dict(domain=1,inputs=inputs,output=level['output'],blocks=[dict(before=before,after=after)]),nodes=[],
        expressions=[dict(source=list(h),terms=lc) for h,lc in sorted(observed.items())])


class NoteTreeTests(unittest.TestCase):
    def test_all48_exact_sources_and_first_last_actual_rows(self):
        obj,note,caller,stream,_=tree_fixture();checked=tree.inspect_metadata(encoded(obj),note,caller)
        self.assertEqual(len(checked['levels']),48);self.assertLess(len(checked['observed']),4096)
        for slot,index in ((0,0),(0,23),(1,0),(1,23)):
            selected=tree.extract_level(encoded(obj),io.BytesIO(stream.getvalue()),note,caller,slot,index)
            certified=tree.certificates(encoded(obj),selected,note,caller)
            self.assertEqual(len(certified['rows']),15)
            self.assertEqual(len(certified['products']),6)
            generated=tree.generate_level(encoded(obj),selected,note,caller)
            self.assertEqual(generated.count('#print axioms'),8)
            self.assertIn('Tree.wiring_sound',generated)
            self.assertIn('Compiler.checked_product_sound',generated)
            self.assertNotIn('(childrenEq :',generated)
            self.assertNotIn('sorry',generated)

    def test_all_positions_positive_assignment_and_wrong_child_semantic_control(self):
        obj,note,caller,stream,_=tree_fixture()
        rows=tree.extract_level(encoded(obj),stream,note,caller,0,0)['selected_rows']
        for position in range(4):
            low,high=position%2,position//2;node,first,second,third=7,11,13,17
            ls=low*(first-node);rs=low*(third-node)
            bases=[node+ls,first-ls,second,third]
            deltas=[first-bases[0],second-bases[1],node+rs-second,-rs]
            outputs=[ls,rs,*[high*d for d in deltas]]
            rho={0:1,4000:1,960:node,731:low,732:high,1203:first,1204:second,1205:third}
            for j,((a,b,_),output) in enumerate(zip(tree.inspect_metadata(encoded(obj),note,caller)['levels'][0]['products'],outputs)):
                evaluate=lambda terms:sum(rho.get(c,0)*v for c,v in terms)%relation.MODULUS
                rho[2500+j]=output%relation.MODULUS;rho[3100+j]=(evaluate(a)-evaluate(b))**2%relation.MODULUS
            satisfy=lambda:all(evaluate([(c,int(v,16)) for c,v in row['a']])**2%relation.MODULUS==
                               evaluate([(c,int(v,16)) for c,v in row['b']]) for row in rows)
            self.assertTrue(satisfy())
            expected=[first,second,third];expected.insert(position,node)
            children=[evaluate(lc) for lc in tree.inspect_metadata(encoded(obj),note,caller)['levels'][0]['children']]
            self.assertEqual(children,expected)
            rho[2502]=(rho[2502]+1)%relation.MODULUS
            self.assertFalse(satisfy())

    def test_source_order_policy_products_and_persisted_rows_refused(self):
        obj,note,caller,stream,_=tree_fixture()
        mutations=[lambda o:o.update(depth=23),lambda o:o['levels'].reverse(),
            lambda o:o['levels'][1].update(node=o['levels'][0]['node']),
            lambda o:o['levels'][0].update(low=o['levels'][0]['high']),
            lambda o:o['levels'][0]['products'][2].__setitem__(1,o['levels'][0]['products'][3][1]),
            lambda o:o['levels'][0]['children'].reverse(),lambda o:o['expressions'].pop(),
            lambda o:o.update(repeated_observations_equal=False)]
        for mutation in mutations:
            changed=copy.deepcopy(obj);mutation(changed)
            with self.assertRaises(relation.RelationError):tree.inspect_metadata(encoded(changed),note,caller)
        selected=tree.extract_level(encoded(obj),stream,note,caller,0,0)
        for i in range(15):
            changed=copy.deepcopy(selected);changed['selected_rows'].pop(i)
            with self.subTest(omitted=i),self.assertRaises(relation.RelationError):tree.certificates(encoded(obj),changed,note,caller)

    def test_combined_qualified_view_digest_order_and_hash_child_join(self):
        obj,note,caller,_,_=tree_fixture();pending=copy.deepcopy(obj)
        pending.update(ordinary_full_ordered_rows_equal=False,repeated_observations_equal=False)
        pending['spend'].update(ordinary_full_ordered_rows_equal=False,repeated_observations_equal=False)
        data=encoded(pending);hash_body=state_page(obj,0);hash_data=encoded(hash_body)
        manifest=dict(schema='shieldd-transfer-note-t4-pages-v1',family='transfer',scope=pages.SCOPE,
            **{k:obj[k] for k in ('relation_digest','domain_size','full_rows','constant_copy')},
            ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True,
            pages=[dict(ordinal=i,slot=s,role=r,level=l,block=b,blake3=blake3(hash_data).hexdigest())
                   for i,(s,r,l,b) in enumerate(hash_pages.inventory())]+[
                dict(ordinal=55,slot=0,role='tree',level=0,block=0,blake3=blake3(data).hexdigest())])
        view,note_view=pages.qualified_tree(encoded(manifest),data,caller)
        pages.qualified_hash(encoded(manifest),hash_data,3,view,note_view,caller)
        self.assertFalse(json.loads(data)['spend']['ordinary_full_ordered_rows_equal'])
        for mutation in (lambda m:m['pages'].pop(),lambda m:m['pages'][55].update(ordinal=54),
                         lambda m:m.update(ordinary_full_ordered_rows_equal=False)):
            changed=copy.deepcopy(manifest);mutation(changed)
            with self.assertRaises(relation.RelationError):pages.qualified_tree(encoded(changed),data,caller)
        with self.assertRaisesRegex(relation.RelationError,'bytes/digest'):pages.qualified_tree(encoded(manifest),data+b' ',caller)
        changed=copy.deepcopy(hash_body);changed['hash']['inputs'][1:]=list(reversed(changed['hash']['inputs'][1:]))
        # Rebuild absorbed boundaries so the failure is child routing, not an unrelated capacity mismatch.
        changed['hash']['blocks'][0]['before'][2:]=changed['hash']['inputs'][1:]
        changed.update(ordinary_full_ordered_rows_equal=True,repeated_observations_equal=True)
        with self.assertRaisesRegex(relation.RelationError,'exact source order'):
            tree.inspect_hash_link(view,encoded(changed),note_view,caller)

    def test_fresh_tree_hook_preserves_owned_operation_and_fullrow_qualifier(self):
        base=Path('tests/fixtures/current-note-tree.rs').read_bytes()
        result=hooks.instrument_tree(base)
        self.assertEqual(result.count(b'params.circuit(kind as u8, &inputs)'),1)
        self.assertLess(result.index(b'let next = params.circuit'),result.index(b'note_inspection::record'))
        self.assertLess(result.index(b'note_inspection::record'),result.index(b'node = next'))
        with self.assertRaises(ValueError):hooks.instrument_tree(result)
        with self.assertRaises(ValueError):hooks.instrument_tree(base.replace(b'node = params',b'node = other'))
        exporter=Path('tests/fixtures/current-transfer-ownership-inspection.rs').read_bytes()
        exporter=spend_hooks.instrument_exporter(exporter,Path('integration/observers/note_spend_export.rs').read_bytes())
        exporter=hash_hooks.instrument_exporter(exporter,Path('integration/observers/note_hash_export.rs').read_bytes())
        exporter=hash_hooks.instrument_pages_exporter(exporter,Path('integration/observers/note_hash_pages_export.rs').read_bytes())
        result=hooks.instrument_exporter(exporter,Path('integration/observers/note_t4_pages_export.rs').read_bytes())
        self.assertEqual(result.count(b'compare_framed_rows(&paths[0], path, 200770, 262144)?;'),1)
        self.assertIn(b'qualify_note_t4_pages(first,repeated,&pending)?;',result)
        self.assertIn(b'qualify_note_hash_pages(first,repeated,&pending)?;',result)
        self.assertIn(b'note-hash-spool',result);self.assertIn(b'note-hash-pages-spool',result)
        with self.assertRaises(ValueError):hooks.instrument_exporter(result,b'')


if __name__=='__main__':unittest.main()
