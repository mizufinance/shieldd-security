"""Bounded pure frame/source fixtures, never genuine runtime qualification."""
import copy,unittest
from circuits import transfer_balance_native_composition as native
from circuits import transfer_relation as relation


def fixture():
    identity={'fixture':'synthetic original polynomials; no capture/qualification'}
    outgoing=(('source',(1,100)),('source',(1,101)))
    unsigned=(((100,1),),((101,1),));blinded=(((200,1),),((201,1),))
    rows={0:(((6,1),),()),1:(((100,1),),()),2:(((200,1),),()),3:(((300,1),),())}
    v=dict(identity=identity,seed_writes=[10,11],writes=[10,11,100,101],rows=[1],
        protected=[0,1,2,6,7,8,200692],
        programs=[{'outgoing':outgoing}]*65,
        checked={'chunks':[{'derived':{(1,100):unsigned[0],(1,101):unsigned[1]}}]})
    b=dict(identity=identity,canonical={'writes':[150],'rows':[]},
        loop={'programs':[{'output':blinded}]*126,'writes':[200,201],'rows':[2]})
    f=dict(identity=identity,parents={'fixture':'source-only'},writes=[300,301],
        selected_rows=[{'row':3}],roles=dict(negative=((7,1),),unsigned=unsigned,blinded=blinded))
    return v,b,f,rows,identity


class NativeCompositionTests(unittest.TestCase):
    def test_prior_rows_and_seed_reuse_remain_explicit(self):
        joined=native._join(*fixture())
        self.assertEqual(joined['incoming_rows'],[0])
        self.assertEqual(joined['variable_writes'],[100,101])
        self.assertEqual(joined['seed_columns'],[10,11])
        self.assertEqual(joined['rows'],[0,1,2,3])
        self.assertIn('semantic identity required',joined['seed_strategy'])
        self.assertNotIn('qualified',joined)
        self.assertNotIn('satisfies',joined)

    def test_h_and_final_preserve_preceding_actual_polynomials(self):
        for kind in ('h','final','shared','overlap','incoming'):
            values=list(copy.deepcopy(fixture()));v,b,f,rows,_=values
            if kind=='h':b['loop']['writes'].append(100)
            elif kind=='final':f['writes'].append(200)
            elif kind=='shared':b['canonical']['writes'].append(6)
            elif kind=='overlap':f['writes'].append(101)
            else:rows[0]=(((150,1),),())
            with self.subTest(kind=kind),self.assertRaises(relation.RelationError):native._join(*values)

    def test_exact_endpoint_source_lcs_and_row_identity_refuse(self):
        for kind in ('output','identity','coverage'):
            values=list(copy.deepcopy(fixture()));v,b,f,rows,_=values
            if kind=='output':f['roles']['unsigned']=(((102,1),),((101,1),))
            elif kind=='identity':b['identity']={'fixture':'changed'}
            else:del rows[1]
            with self.subTest(kind=kind),self.assertRaises(relation.RelationError):native._join(*values)

    def test_h_preserves_sign_even_when_variable_rows_do_not_read_it(self):
        values=list(copy.deepcopy(fixture()))
        values[1]['canonical']['writes'].append(7)
        with self.assertRaisesRegex(relation.RelationError,'earlier signed/shared roles'):
            native._join(*values)

    def test_final_preserves_owned_magnitude_outside_group_row_support(self):
        # Absence from the group rows is not freshness for the independently
        # owned magnitude and its signed reconstruction rows.
        values=list(copy.deepcopy(fixture()))
        values[2]['writes'].append(8)
        with self.assertRaisesRegex(relation.RelationError,'earlier signed/shared roles'):
            native._join(*values)

    def test_final_preserves_full_canonical_rows_not_only_fixed_windows(self):
        values=list(copy.deepcopy(fixture()));v,b,f,rows,identity=values
        # A comparator product/assertion row is outside the fixed-window
        # projection. It still belongs to the H constructor's full claim.
        rows[4]=(((150,1),),())
        b['canonical']['rows']=[4]
        joined=native._join(*values)
        self.assertIn(4,joined['blinding_rows'])
        f['writes'].append(150)
        with self.assertRaises(relation.RelationError):native._join(*values)

    def test_canonical_derivative_requires_its_explicit_original_certificate_view(self):
        from tests.test_transfer_balance_blinding_canonical import fixture as canonical_fixture
        from circuits import transfer_balance_blinding_canonical as scalar
        _,checked,_,identity,raw,normalized,records=canonical_fixture()
        derivative=scalar._derive(checked,identity,raw,normalized,records)
        self.assertNotIn('selected_rows',derivative)
        retained=native._rows([derivative['certificate']])
        self.assertEqual(set(retained),set(raw))

    def test_lifecycle_bool_cannot_claim_a_replay(self):
        with self.assertRaisesRegex(relation.RelationError,'ONE joint replay'):
            native.plan(b'',[],b'',[],b'',b'',{}, {},[],[],{'ordinary_replays':True})

    def test_one_empty_qualifier_cannot_be_promoted_by_marker(self):
        with self.assertRaises(relation.RelationError):
            native.plan(b'',[],b'',[],b'',b'',{}, {},[],[],{'ordinary_replays':1})


if __name__=='__main__':unittest.main()
