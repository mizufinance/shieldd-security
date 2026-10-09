"""Small folded source fixtures; no actual capture/SDK generator/kernel credit."""
import copy,hashlib,json,unittest
import blake3
from circuits import transfer_epk_fixed as epk,transfer_relation as relation
from tests.test_transfer_epk_fixed import fixture,encoded,native,source

def all_fixture():
    raw=[];scopes=[];descriptors=[];entries=[];all_observed={};caller=None
    for scope_id in range(6):
        obj,capsules,caller0=fixture();lane,slot=('recovery',scope_id) if scope_id<2 else ('encryption',scope_id-2)
        offset=1000*scope_id;identity=[native(0),native(1)]
        obj.update(lane=lane,slot=slot,output=identity,randomizer=source(offset),inverse=source(offset+404),
            published=[source(offset+402),source(offset+403)],bits=[[1,offset+i] for i in range(10,262)],
            ordinary_full_ordered_rows_equal=False,repeated_observations_equal=False)
        handles={(1,offset+i) for i in [0,402,403,404,*range(10,262)]}
        observed={h:((h[1]+3,1),) for h in handles};all_observed.update(observed)
        obj['expressions']=[dict(source=list(h),terms=[[h[1]+3,f'{1:064x}']]) for h in sorted(handles)]
        scopes.append({k:obj[k] for k in ('lane','slot','randomizer','published','output','inverse')})
        if scope_id<2:entries.append(dict(randomizer=obj['randomizer'],bits=obj['bits'],capsule=obj['published'],computed_epk=identity,epk_inverse=obj['inverse']))
        for local in range(8):
            start=16*local;count=min(16,126-start);page=copy.deepcopy(obj)
            page.update(window_start=start,window_count=count,windows=[])
            for index in range(start,start+count):
                w=copy.deepcopy(obj['windows'][0]);w.update(index=index,bits=obj['bits'][2*index:2*index+2]);page['windows'].append(w)
            data=encoded(page);raw.append(data);ordinal=len(raw)-1
            descriptors.append(dict(ordinal=ordinal,scope_id=scope_id,window_start=start,window_count=count,blake3=blake3.blake3(data).hexdigest()))
        caller=caller0
    parent={k:caller['metadata'][k] for k in (*epk.IDENTITY,'ordinary_full_ordered_rows_equal','repeated_observations_equal')}
    parent.update(schema='shieldd-transfer-epk-all-fixed-pages-v1',family='transfer',scope=epk.ALL_PARENT_SCOPE,scopes=scopes,pages=descriptors)
    capsules=dict(metadata=dict(caller['metadata'],schema='shieldd-transfer-recovery-capsule-roles-v1',capsules=entries),observed=all_observed,metadata_sha256='a'*64)
    return parent,raw,capsules,caller

class AllEpkPagesTests(unittest.TestCase):
    def test_complete_six_scopes_keep_pending_byte_identity(self):
        parent,raw,capsules,caller=all_fixture();data=encoded(parent)
        checked=epk.inspect_all_pages(data,raw,capsules,caller)
        self.assertEqual([(s['lane'],s['slot']) for s in checked['scopes']],[('recovery',0),('recovery',1),*[('encryption',i) for i in range(4)]])
        self.assertEqual(sum(len(c['points']) for s in checked['scopes'] for c in s['chunks']),6*126)
        self.assertEqual(checked['parent_sha256'],hashlib.sha256(data).hexdigest())
        self.assertEqual(checked['raw_page_sha256'],[hashlib.sha256(d).hexdigest() for d in raw])
        self.assertTrue(all(c['metadata']['ordinary_full_ordered_rows_equal'] is False for s in checked['scopes'] for c in s['chunks']))
        self.assertIn('native encryption object association OPEN',checked['scope'])

    def test_missing_reordered_scopes_and_false_parent_refused(self):
        for edit in ('missing','order','scope','flag','endpoint','digest','extra'):
            parent,raw,capsules,caller=all_fixture()
            if edit=='missing':raw.pop()
            elif edit=='order':parent['pages'][8]['scope_id']=0
            elif edit=='scope':parent['scopes'][2]['slot']=3
            elif edit=='flag':parent['ordinary_full_ordered_rows_equal']=False
            elif edit=='endpoint':parent['scopes'][5]['inverse']=source(1)
            elif edit=='digest':parent['relation_digest']='f'*64
            else:parent['ignored']=True
            with self.subTest(edit=edit),self.assertRaises(relation.RelationError):epk.inspect_all_pages(encoded(parent),raw,capsules,caller)

    def test_semantic_table_quotient_and_lc_edit_rehash_still_refused(self):
        for edit in ('table','quotient','lc','private','continuity','rawflag','ast'):
            parent,raw,capsules,caller=all_fixture();ordinal=17;obj=json.loads(raw[ordinal])
            if edit=='table':obj['windows'][0]['table'][1]=[native(1),native(1)]
            elif edit=='quotient':obj['windows'][0]['quotient'][0]=native(1)
            elif edit=='lc':obj['expressions'][0]['terms'][0][1]=f'{2:064x}'
            elif edit=='private':obj['bits'][0]=[1,10]
            elif edit=='continuity':obj['windows'][0]['points'][0]=[native(0),native(-1)]
            elif edit=='rawflag':obj['ordinary_full_ordered_rows_equal']=True
            else:obj['nodes']=[dict(index=999,multiply=True,left=[1,10],right=[1,11])]
            raw[ordinal]=encoded(obj);parent['pages'][ordinal]['blake3']=blake3.blake3(raw[ordinal]).hexdigest()
            with self.subTest(edit=edit),self.assertRaises(relation.RelationError):epk.inspect_all_pages(encoded(parent),raw,capsules,caller)
