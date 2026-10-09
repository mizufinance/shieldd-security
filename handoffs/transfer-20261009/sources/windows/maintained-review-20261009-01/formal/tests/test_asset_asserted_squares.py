"""Deferred square source/row correspondence; tiny fixtures, no runtime claim."""
import copy
import hashlib
import io
import json
from pathlib import Path
import unittest
from blake3 import blake3
from circuits import transfer_asset_map as maps, transfer_relation as relation
from circuits.transfer_balance_rows import canonical, combine
from integration import asset_asserted_square_observer as observer
from integration.recovery_t4_capture import _function
from tests.test_transfer_asset_map import fixture, encoded
from tests.test_transfer_asset_generator_nonidentity import inverse_fixture
from circuits import transfer_asset_generator_nonidentity as nonidentity


def deferred_fixture():
    data, caller, stream, _, builder = fixture(17)
    return defer_captured(data,caller,stream.getvalue(),builder)


def defer_captured(data, caller, raw, builder):
    obj=json.loads(data); records=[json.loads(line) for line in raw.splitlines()]
    squares=[(obj['qr'][0],obj['values'][9],obj['qr'][1]),
             (obj['constraint_products'][0],obj['values'][12],obj['values'][11])]
    copy_column=obj['constant_copy']
    outline=lambda lc:canonical((copy_column if c==0 else c,n) for c,n in lc)
    rows=[(canonical((c,int(n,16)) for c,n in row['a']),canonical((c,int(n,16)) for c,n in row['b'])) for row in records[1:-1]]
    for square,base,target in squares:
        rows.remove((outline(builder.lc(base)),outline(builder.lc(square))))
        rows.remove((outline(combine(builder.lc(square),builder.lc(target),-1)),()))
        rows.append((outline(builder.lc(base)),outline(builder.lc(target))))
    obj['schema']=obj['schema'].replace('-v1','-v2')
    obj['asserted_squares']=[dict(square=s,base=b,target=t) for s,b,t in squares]
    obj['expressions']=[e for e in obj['expressions'] if all(e['source']!=s['source'] for s,_,_ in squares)]
    header=records[0]; domain=obj['domain_size'];digest=blake3()
    digest.update(relation.NAMESPACE+relation.u64(domain)+relation.u64(len(rows))+
        relation.indices(header['source_public'])+relation.u64(1)+relation.indices(header['source_blocks'][0]))
    records=[dict(row=i,a=[[c,f'{n:064x}'] for c,n in a],b=[[c,f'{n:064x}'] for c,n in b]) for i,(a,b) in enumerate(rows)]
    for row in records:digest.update(b'A'+relation.terms(row['a'],domain)+b'B'+relation.terms(row['b'],domain))
    obj.update(relation_digest=digest.hexdigest(),full_rows=len(rows));caller=copy.deepcopy(caller)
    caller['metadata'].update(relation_digest=digest.hexdigest(),full_rows=len(rows))
    header.update(relation_digest=digest.hexdigest(),stored_rows=len(rows))
    raw=b''.join(encoded(v) for v in [header,*records,dict(eof=True,rows=len(rows))])
    return encoded(obj),caller,raw,builder


class DeferredSquareTests(unittest.TestCase):
    def test_nonidentity_v2_derivative_keeps_companions_and_exact_parent(self):
        data,caller,stream,b,_=inverse_fixture()
        data,caller,raw,b=defer_captured(data,caller,stream.getvalue(),b)
        checked=nonidentity.inspect_metadata(data,caller)
        view=nonidentity.derived_map_view(data,caller)
        self.assertEqual(view['parent_metadata_sha256'],hashlib.sha256(data).hexdigest())
        self.assertEqual(json.loads(view['map_data'])['schema'],'shieldd-transfer-asset-map-v2')
        self.assertEqual(json.loads(view['map_data'])['asserted_squares'],json.loads(data)['asserted_squares'])
        extracted=nonidentity.extract(data,io.BytesIO(raw),caller)
        self.assertEqual(len(extracted['selected_rows']),4)
        nonidentity.certificates(data,extracted,caller)
        maps.certificates(view['map_data'],maps.extract(view['map_data'],io.BytesIO(raw),caller),caller)

    def test_companions_require_actual_direct_rows_not_output_lcs(self):
        data,caller,raw,b=deferred_fixture();checked=maps.inspect_metadata(data,caller)
        self.assertEqual(len(checked['asserted_square_nodes']),2)
        self.assertTrue(set(checked['asserted_square_nodes']).isdisjoint(checked['captured_observed']))
        extracted=maps.extract(data,io.BytesIO(raw),caller)
        certificates=maps.certificates(data,extracted,caller)
        self.assertEqual(extracted['identity']['raw_sha256'],hashlib.sha256(raw).hexdigest())
        for square,(base,target) in checked['asserted_square_nodes'].items():
            self.assertEqual(b.val({'source':list(base)})**2 % relation.MODULUS,b.val({'source':list(target)}))
            cert=next(c for c in certificates['nonlinear'] if c['node']==square[1])
            self.assertEqual(len(cert['rows']),1)
        # Replacing a mandatory original square row is a semantic row failure,
        # not a fabricated LC or a metadata-only correspondence.
        damaged=copy.deepcopy(extracted)
        first=next(c for c in certificates['nonlinear'] if (2,c['node']) in checked['asserted_square_nodes'])
        damaged['selected_rows']=[row for row in damaged['selected_rows'] if row['row'] not in first['rows']]
        with self.assertRaises(relation.RelationError):maps.certificates(data,damaged,caller)

    def test_closed_roles_output_lc_and_ast_refuse(self):
        data,caller,_,b=deferred_fixture();original=json.loads(data)
        changes=[lambda o:o['asserted_squares'].reverse(),
                 lambda o:o['asserted_squares'][0].update(base=o['values'][12]),
                 lambda o:o['asserted_squares'][0].update(extra=True),
                 lambda o:o['expressions'].append(dict(source=o['qr'][0]['source'],terms=[[c,f'{n:064x}'] for c,n in b.lc(o['qr'][0])])),
                 lambda o:next(n for n in o['nodes'] if n['index']==o['qr'][0]['source'][1]).update(multiply=False)]
        for mutate in changes:
            changed=copy.deepcopy(original);mutate(changed)
            with self.assertRaises(relation.RelationError):maps.inspect_metadata(encoded(changed),caller)

    def test_fresh_child_preserves_unrelated_source_and_lifecycle(self):
        root=Path(__file__).resolve().parents[1]
        packet=root/'.work/diagnostics/transfer-implementation-20261002/transfer-t4-future-gaps-source-04/overlay'
        old=(packet/'crates/crypto/circuits/examples/transfer-ownership-inspection.rs').read_bytes()
        new=observer.exporter(old).decode();oldtext=old.decode().replace('\r\n','\n')
        for name in ('capture_transfer_t4_recovery_pages','qualify_recovery_t4_pages','capture_transfer_t4_pages'):
            self.assertEqual(_function(new,name),_function(oldtext,name))
        self.assertIn('qualify_asset_asserted_squares(&pending)?;',new)
        for name in ('asset_map_catalogue.rs','asset_nonidentity_catalogue.rs'):
            source=(packet/'crates/crypto/circuits/src'/name).read_bytes()
            result=observer.catalogue(source).decode()
            self.assertIn('selected.remove(square)',result)
            self.assertIn('.chain(asserted_squares.iter().map(|s| s.0))',result)
            self.assertIn('asserted square reused as source operand',result)
            self.assertEqual(result.count('Relation::compile_inspected(&c, &layout, &selected)?'),1)
            self.assertIn('16384',result);self.assertIn('4096',result)
            with self.assertRaises(ValueError):observer.catalogue(result.encode())
        with self.assertRaises(ValueError):observer.exporter(new.encode())


if __name__=='__main__':unittest.main()
