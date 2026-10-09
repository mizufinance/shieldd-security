"""Small folded row fixtures; matcher spy tests orchestration, not runtime replay."""
import copy,unittest
from unittest.mock import patch
from circuits import transfer_epk_fixed as epk,transfer_epk_fixed_batch as batch,transfer_relation as relation
from tests.test_transfer_epk_all_fixed import all_fixture
from tests.test_transfer_epk_fixed import encoded

def selected_fixture():
    parent,raw,capsules,caller=all_fixture();checked=epk.inspect_all_pages(encoded(parent),raw,capsules,caller)
    required,products,squares,prefixes=batch._requirements(checked);assert products==[] and squares==[]
    # Every native-identity table folds. Only6*252 Boolean rows +one shared
    # copy link are exercised; lawful generator/native/actual replay are OPEN.
    rows=[dict(row=i,a=[[c,f'{v:064x}'] for c,v in a],b=[[c,f'{v:064x}'] for c,v in b]) for i,(a,b) in enumerate(required)]
    combined=dict(identity=dict(relation_digest=parent['relation_digest'],domain_size=262144,stored_rows=200770),
        templates=[dict(roles=names,row=i) for i,names in enumerate(required.values())],products=[],selected_rows=rows)
    return checked,combined,prefixes,(parent,raw,capsules,caller)

class EpkBatchTests(unittest.TestCase):
    def test_shared_rows_and_complete48_projections(self):
        checked,combined,prefixes,_=selected_fixture();result=batch._partition(checked,combined,prefixes)
        self.assertEqual(len(result['selected_rows']),6*252+1)
        self.assertEqual(len(result['pages']),48)
        self.assertEqual([len(p['rows']) for p in result['pages']],[33]*7+[29]+([33]*7+[29])*5)
        for i in (0,7,8,15,16,47):
            page=batch.page_selection(checked,result,i)
            self.assertEqual(page['metadata_sha256'],checked['scopes'][i//8]['chunks'][i%8]['metadata_sha256'])
        # Each retained Boolean row holds for two independent scalar bit
        # assignments; no arbitrary surrounding-row preservation is inferred.
        for value in (0,1):
            rho=lambda c:1 if c in (0,200692) else value
            for row in result['selected_rows']:
                a,b=(sum(rho(c)*int(v,16) for c,v in row[side])%relation.MODULUS for side in ('a','b'))
                self.assertEqual(a*a%relation.MODULUS,b)

    def test_one_matcher_invocation_and_reaccept_all_raw_flags(self):
        checked,combined,prefixes,(parent,raw,capsules,caller)=selected_fixture()
        sentinel=object()
        with patch.object(batch.arithmetic,'extract_templates',return_value=combined) as matcher:
            result=batch.extract_rows(encoded(parent),raw,capsules,caller,sentinel)
            matcher.assert_called_once();self.assertIs(matcher.call_args.args[0],sentinel)
        self.assertEqual(result['raw_page_sha256'],checked['raw_page_sha256'])
        parent['repeated_observations_equal']=False
        with patch.object(batch.arithmetic,'extract_templates') as matcher:
            with self.assertRaises(relation.RelationError):batch.extract_rows(encoded(parent),raw,capsules,caller,sentinel)
            matcher.assert_not_called()

    def test_missing_extra_or_mutated_original_rows_refused(self):
        for edit in ('missing','extra','boolean','identity','coverage'):
            checked,combined,prefixes,_=selected_fixture()
            if edit=='missing':combined['selected_rows'].pop()
            elif edit=='extra':combined['selected_rows'].append(dict(row=190000,a=[[7,f'{1:064x}']],b=[]))
            elif edit=='boolean':combined['selected_rows'][1]['b']=[]
            elif edit=='identity':combined['identity']['relation_digest']='f'*64
            else:combined['templates'].pop()
            with self.subTest(edit=edit),self.assertRaises(relation.RelationError):batch._partition(checked,combined,prefixes)

    def test_persisted_projection_preserves_parent_identity(self):
        checked,combined,prefixes,_=selected_fixture();result=batch._partition(checked,combined,prefixes)
        for edit in ('parent','rawpage','descriptor','rows','canonical'):
            changed=copy.deepcopy(result)
            if edit=='parent':changed['parent_sha256']='f'*64
            elif edit=='rawpage':changed['raw_page_sha256'][0]='f'*64
            elif edit=='descriptor':changed['pages'][0]['scope_id']=1
            elif edit=='rows':changed['pages'][0]['rows'].reverse()
            else:changed['include_canonical']=True
            with self.subTest(edit=edit),self.assertRaises(relation.RelationError):batch.page_selection(checked,changed,0)
