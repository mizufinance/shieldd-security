"""Full-digest synthetic controls and scoped semantic omission counterexamples."""
import copy
import io
import json
import unittest
from blake3 import blake3
from circuits import transfer_relation as relation
from circuits import transfer_encryption_registered_guard as guard
from circuits import generate_transfer_encryption_registered_guard as renderer
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_encryption_dh_keys import fixture as keys


def fixture(change=None):
    checked = keys()
    for handle,(multiply,left,right) in sorted(checked['nodes'].items()):
        checked['derived'][handle] = ((200+handle[1],1),) if multiply else combine(checked['derived'][left],checked['derived'][right])
    x,y,flag = ((6,1),),((7,1),),((3,1),)
    copy_column,domain = 3500,4096
    rows = [(canonical([(0,1),(copy_column,-1)]),())]
    def product(left,right,aux,out):
        rows.extend([(combine(left,right,-1),((aux,1),)),
                     (combine(left,right),canonical([(aux,1),(out,4)]))])
    for operand,zero,inverse,aux,out in ((x,100,101,102,103),
                                      (combine(y,guard.ONE,-1),110,111,112,113)):
        rows.append((((zero,1),),((zero,1),)))
        product(operand,((inverse,1),),aux,out)
        rows.append((canonical([(out,1),(0,-1),(zero,1)]),()))
    product(((100,1),),((110,1),),120,121)
    product(flag,((121,1),),122,123)
    rows.append((((123,1),),()))
    if change == 'x_equation':
        rows[4] = (canonical([(103,1),(0,-2),(100,1)]),())
    elif change == 'y_equation':
        rows[8] = (canonical([(113,1),(0,-1),(110,2)]),())
    elif change == 'missing_and':
        rows[10] = ((),())
    elif change == 'assertion':
        rows[-1] = (canonical([(123,1),(0,-1)]),())
    elif change == 'link':
        rows[0] = ((),())
    elif change == 'orientation':
        rows[2] = (canonical((c,-v) for c,v in rows[2][0]),rows[2][1])
        rows[-1] = (canonical([(123,-1)]),())
    elif change == 'bound':
        rows.extend((combine(x,((2000+i,1),),-1),((2200+i,1),)) for i in range(65))
    outline = lambda lc: canonical((copy_column if c == 0 else c,v) for c,v in lc)
    encode = lambda lc: [[c,f'{v:064x}'] for c,v in lc]
    records = [dict(row=i,a=encode(a if i == 0 else outline(a)),b=encode(b if i == 0 else outline(b)))
               for i,(a,b) in enumerate(rows)]
    public,blocks = [[1,100]],[[[1,101]]]
    digest = blake3(relation.NAMESPACE+relation.u64(domain)+relation.u64(len(records))+
                    relation.indices(public)+relation.u64(1)+relation.indices(blocks[0]))
    for row in records:
        digest.update(b'A'+relation.terms(row['a'],domain)+b'B'+relation.terms(row['b'],domain))
    identity = digest.hexdigest()
    header = dict(schema='shieldd-transfer-relation-v1',family='transfer',relation_digest=identity,
        domain_size=domain,stored_rows=len(records),public_inputs=1,committed_blocks=[1],
        constant_column=0,public_columns=[1],committed_columns=[[2]],source_public=public,
        source_blocks=blocks,coefficient_encoding='canonical-big-endian-32',field_modulus=str(relation.MODULUS),
        role_provenance='constant0/public prefix and committed_start=1+public_count in exact compiler',
        padding='implicit-all-zero-rows-to-domain-size')
    data = b''.join(json.dumps(item).encode()+b'\n' for item in [header,*records,dict(eof=True,rows=len(records))])
    checked.update(metadata=dict(schema='shieldd-transfer-encryption-dh-v1',role=0,
        relation_digest=identity,domain_size=domain,full_rows=len(records),constant_copy=copy_column),
        metadata_sha256='a'*64)
    return checked,data


class RegisteredGuardTests(unittest.TestCase):
    def test_complete_replays_and_persisted_certificate_render_without_nonidentity_premise(self):
        for change in (None,'orientation'):
            checked,data = fixture(change)
            calls = []
            def stream():
                calls.append(True)
                return io.BytesIO(data)
            result = guard.extract(checked,stream)
            self.assertEqual(len(calls),2)
            self.assertEqual(len(result['selected_rows']),12)
            persisted = json.loads(json.dumps(result))
            name,source = renderer.generate(checked,persisted)
            self.assertEqual(name,'RuntimeTransferEncryptionRegisteredPayloadGuard')
            self.assertIn('#check @regulated_nonidentity',source)
            self.assertIn('satisfied : Satisfies rho rawRows',source)
            signature = source.split('theorem regulated_nonidentity',1)[1].split(':= by',1)[0]
            self.assertNotIn('nonzero',signature)
            self.assertNotIn('point rho ≠',signature.split(': point rho',1)[0])

    def test_each_missing_or_changed_semantic_obligation_and_bound_is_refused(self):
        for change in ('x_equation','y_equation','missing_and','assertion','link','bound'):
            checked,data = fixture(change)
            with self.subTest(change=change),self.assertRaises(relation.RelationError):
                guard.extract(checked,lambda:io.BytesIO(data))

    def test_changed_persisted_rows_roles_and_certificate_are_refused(self):
        checked,data = fixture()
        extracted = guard.extract(checked,lambda:io.BytesIO(data))
        for change in ('row','point','flag','certificate'):
            bad = copy.deepcopy(extracted)
            if change == 'row':
                bad['selected_rows'][-1]['a'][0][1] = f'{2:064x}'
            elif change == 'point':
                bad['point'] = (((9,1),),bad['point'][1])
            elif change == 'flag':
                bad['flag'] = ((4,1),)
            else:
                bad['certificate']['zero_x'] = ((999,1),)
            with self.subTest(change=change),self.assertRaises(relation.RelationError):
                renderer.generate(checked,bad)
        checked['qualified'] = False
        with self.assertRaises(relation.RelationError):
            guard.extract(checked,lambda:self.fail('pending capture reached replay'))

    def test_identity_counterexamples_fail_only_intended_omitted_equation(self):
        checked,data = fixture()
        selected = guard.extract(checked,lambda:io.BytesIO(data))['selected_rows']
        p = relation.MODULUS
        def rejected(zero_x,zero_y):
            rho = {0:1,3500:1,3:1,6:0,7:1,100:zero_x,110:zero_y,101:0,111:0}
            rho.update({102:0,103:0,112:0,113:0,120:(zero_x-zero_y)**2 % p,
                        121:zero_x*zero_y % p})
            rho[122] = (rho[3]-rho[121])**2 % p
            rho[123] = rho[3]*rho[121] % p
            evaluate = lambda terms: sum(int(v,16)*rho.get(c,0) for c,v in terms)%p
            return {row['row'] for row in selected if evaluate(row['a'])**2%p != evaluate(row['b'])}
        # Each assignment has regulated=1 and the forbidden identity (x,y)=(0,1).
        # Every other selected physical equation holds; the named omission alone
        # would admit the invalid point. These are scoped modular counterexamples.
        self.assertEqual(rejected(0,1),{4})
        self.assertEqual(rejected(1,0),{8})
        self.assertEqual(rejected(1,1),{13})
