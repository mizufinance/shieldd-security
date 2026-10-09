"""Toy physical rows only; never actual captures, qualification or kernels."""
import copy,unittest
from unittest.mock import patch
from blake3 import blake3
from circuits import transfer_remaining_pages as pages,transfer_remaining_tree_bundle as bundle
from circuits.transfer_relation import RelationError
from tests.test_transfer_remaining_pages import tree_position_fixture,encoded


def fixture():
    m,p,a,_=tree_position_fixture()
    root={'source':[1,62000]}
    for item in p['records']:
        if item['scope']=='sender' and item['tag']=='computed-root':item['values'][0]=root
        if item['scope']=='sender' and item['tag']=='tree-level' and item['ordinal']==15:item['values'][12]=root
    hashes=[h for h in p['calls'] if h['scope']=='sender']
    hashes[-1]['output']=hashes[-1]['blocks'][-1]['after'][1]=root
    handles=sorted({tuple(v['source']) for r in p['records'] if r['scope'] in ('sender','caller') for v in r['values'] if 'source' in v})
    p['expressions']=[dict(source=list(h),terms=[[h[1]+3,f'{1:064x}']]) for h in handles]
    data=encoded(p);m['pages'][0].update(bytes=len(data),blake3=blake3(data).hexdigest())
    _,requirements=bundle._requirements(encoded(m),data,a,0)
    physical=[]
    for required,products,squares in requirements:
        for row in required:
            if row not in physical:physical.append(row)
        for name,minus,plus,out,numerator in products:
            aux=((72000+len(physical),1),)
            if out is None:out=((73000+len(physical),1),)
            physical.extend([(minus,aux),(plus,pages.combine(aux,out,4))])
            if numerator is not None:physical.append((pages.combine(out,numerator,-1),()))
        if squares:raise AssertionError('toy nonlinear case changed')
    rows=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in left],b=[[c,f'{v:064x}'] for c,v in right]) for i,(left,right) in enumerate(physical)]
    identity=dict(relation_digest=m['relation_digest'],domain_size=m['domain_size'],stored_rows=m['full_rows'])
    def inspect(stream,expected_relation,row_observer):
        if expected_relation!=identity['relation_digest']:raise AssertionError('identity weakened')
        for row in rows:row_observer(row)
        return identity
    return encoded(m),data,a,inspect


class TreeBundleTests(unittest.TestCase):
    def accepted(self):
        manifest,page,accepted,inspect=fixture()
        with patch.object(bundle.arithmetic.relation,'inspect',side_effect=inspect) as replay:
            extracted=bundle.extract(manifest,page,object(),accepted)
        self.assertEqual(replay.call_count,1)
        return manifest,page,accepted,extracted

    def test_one_replay_three_strict_original_components(self):
        manifest,page,accepted,extracted=self.accepted()
        modules=bundle.generate(manifest,page,extracted,accepted)
        self.assertEqual([source.count('#print axioms') for _,source in modules],[9,4,5])
        self.assertEqual(modules[0][1],pages.generate_tree_level(manifest,page,0,extracted['parts']['level'],accepted))
        self.assertEqual(modules[1][1],pages.generate_tree_position(manifest,page,extracted['parts']['position'],accepted))
        self.assertEqual(modules[2][1],pages.generate_membership(manifest,page,extracted['parts']['membership'],accepted))
        self.assertLess(len(extracted['selected_rows']),sum(len(part['selected_rows']) for part in extracted['parts'].values()))

    def test_changed_component_row_and_unused_union_row_refused(self):
        for mode in ('row','unused','identity','shape','flag','scope'):
            manifest,page,accepted,extracted=self.accepted();bad=copy.deepcopy(extracted)
            if mode=='row':bad['parts']['level']['selected_rows'][-1]['a'][0][0]+=1
            elif mode=='unused':
                row=copy.deepcopy(bad['selected_rows'][-1]);row['row']+=1;bad['selected_rows'].append(row)
            elif mode=='identity':bad['parts']['membership']['identity']['stored_rows']-=1
            elif mode=='shape':bad['parts']['position']=None
            elif mode=='flag':bad['ordinary_replays']=True
            else:bad['scope']='receiver'
            with self.assertRaises(RelationError):bundle.generate(manifest,page,bad,accepted)

    def test_nonzero_level_and_bool_selector_refused_before_stream(self):
        manifest,page,accepted,_=fixture()
        for level in (True,1,None):
            with self.assertRaises(RelationError):bundle.extract(manifest,page,object(),accepted,level)

if __name__=='__main__':unittest.main()
