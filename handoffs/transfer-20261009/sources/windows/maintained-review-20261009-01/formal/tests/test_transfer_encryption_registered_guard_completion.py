"""Construct legal branches against twenty actual-format squared rows."""
import copy
import io
import json
import unittest
from blake3 import blake3
from circuits import transfer_encryption_registered_guard as guard
from circuits import transfer_encryption_registered_guard_completion as completion
from circuits import generate_transfer_encryption_registered_guard_completion as renderer
from circuits import transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_encryption_registered_guard import fixture as guard_fixture


def fixture(change=None):
    checked,data = guard_fixture()
    records = [json.loads(line) for line in data.splitlines()]
    header,rows = records[0],records[1:-1]
    copy_column = checked['metadata']['constant_copy']
    encode = lambda lc: [[c,f'{v:064x}'] for c,v in canonical(
        (copy_column if c == 0 else c,v) for c,v in lc)]
    for operand,zero,aux,out in ((((6,1),),100,130,131),
                               (combine(((7,1),),guard.ONE,-1),110,140,141)):
        for a,b in ((combine(operand,((zero,1),),-1),((aux,1),)),
                    (combine(operand,((zero,1),)),canonical([(aux,1),(out,4)])),
                    (((out,1),),())):
            rows.append(dict(row=len(rows),a=encode(a),b=encode(b)))
    if change == 'annihilator':
        rows[-1]['a'] = [[141,f'{2:064x}']]
        rows[-1]['b'] = [[copy_column,f'{1:064x}']]
    elif change == 'missing_boolean':
        rows[1]['a'] = rows[1]['b'] = []
    digest = blake3(relation.NAMESPACE+relation.u64(header['domain_size'])+relation.u64(len(rows))+
                    relation.indices(header['source_public'])+relation.u64(1)+relation.indices(header['source_blocks'][0]))
    for row in rows:
        digest.update(b'A'+relation.terms(row['a'],header['domain_size'])+b'B'+relation.terms(row['b'],header['domain_size']))
    header.update(stored_rows=len(rows),relation_digest=digest.hexdigest())
    checked['metadata'].update(full_rows=len(rows),relation_digest=digest.hexdigest())
    data = b''.join(json.dumps(r).encode()+b'\n' for r in [header,*rows,dict(eof=True,rows=len(rows))])
    return checked,data


class RegisteredGuardCompletionTests(unittest.TestCase):
    def test_exact_twenty_rows_sixteen_writes_and_persisted_certificate(self):
        checked,data = fixture()
        source = lambda:io.BytesIO(data)
        initial = guard.extract(checked,source)
        calls = []
        def third():
            calls.append(True)
            return source()
        result = completion.extract(checked,third,initial)
        self.assertEqual(len(calls),1)
        self.assertEqual(len(result['selected_rows']),20)
        self.assertEqual(len(result['writes']),16)
        completion.recheck(checked,json.loads(json.dumps(result)))
        name,text = renderer.generate(checked,json.loads(json.dumps(result)))
        self.assertEqual(name,'RuntimeTransferEncryptionRegisteredPayloadCompletion')
        self.assertIn('#check @constructs_and_preserves',text)
        self.assertIn('patchAssignment base (values base) fresh',text)
        self.assertIn('column ∉ fresh',text)
        signature = text.split('theorem constructs ',1)[1].split(':= by',1)[0]
        self.assertNotIn('(satisfied',signature)
        self.assertNotIn('Satisfies base',signature)

    def test_constructed_values_satisfy_all_rows_for_both_legal_branches(self):
        checked,data = fixture()
        source = lambda:io.BytesIO(data)
        result = completion.extract(checked,source,guard.extract(checked,source))
        p = relation.MODULUS
        for x,y,regulated in ((0,1,0),(5,7,1),(0,7,1),(5,1,1)):
            with self.subTest(point=(x,y),regulated=regulated):
                rho = {0:1,3500:1,6:x,7:y,3:regulated,999:42}
                for axis,value in (('x',x),('y',(y-1)%p)):
                    zero = int(value == 0)
                    inverse = pow(value,-1,p) if value else 0
                    values = {'zero_':zero,'inverse_':inverse,
                        'reciprocal_output_':value*inverse%p,
                        'reciprocal_auxiliary_':(value-inverse)**2%p,
                        'annihilator_output_':value*zero%p,
                        'annihilator_auxiliary_':(value-zero)**2%p}
                    for prefix,v in values.items():
                        rho[result['writes'][prefix+axis]] = v
                zx,zy = int(x == 0),int((y-1)%p == 0)
                for name,value in (('equal',zx*zy),('equal_auxiliary',(zx-zy)**2),
                                   ('forbidden',regulated*zx*zy),
                                   ('forbidden_auxiliary',(regulated-zx*zy)**2)):
                    rho[result['writes'][name]] = value%p
                evaluate = lambda lc:sum(int(v,16)*rho.get(c,0) for c,v in lc)%p
                self.assertEqual([r['row'] for r in result['selected_rows']
                    if evaluate(r['a'])**2%p != evaluate(r['b'])],[])
                self.assertEqual(rho[999],42)
                self.assertEqual((rho[6],rho[7],rho[3]),(x,y,regulated))

    def test_missing_zero_boolean_or_changed_annihilator_refused(self):
        for change in ('missing_boolean','annihilator'):
            checked,data = fixture(change)
            source = lambda:io.BytesIO(data)
            with self.subTest(change=change),self.assertRaises(relation.RelationError):
                initial = guard.extract(checked,source)
                completion.extract(checked,source,initial)

    def test_persisted_write_alias_missing_row_and_changed_certificate_refused(self):
        checked,data = fixture()
        source = lambda:io.BytesIO(data)
        result = completion.extract(checked,source,guard.extract(checked,source))
        for change in ('alias','row','certificate'):
            bad = copy.deepcopy(result)
            if change == 'alias':
                bad['writes']['inverse_x'] = 6
            elif change == 'row':
                bad['selected_rows'].pop()
            else:
                bad['extra']['x']['annihilator']['assertion'] = 999
            with self.subTest(change=change),self.assertRaises(relation.RelationError):
                completion.recheck(checked,bad)
            with self.subTest(renderer_change=change),self.assertRaises(relation.RelationError):
                renderer.generate(checked,bad)
