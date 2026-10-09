"""Sparse assertion controls; these do not certify the full Transfer relation."""
import unittest
from unittest.mock import patch
from circuits import generate_transfer_statement_public_hash as public
from circuits import transfer_statement_binding as binding
from circuits.transfer_relation import RelationError, MODULUS


def fixture():
    selected = dict(checked=dict(metadata=dict(relation_digest='ab'*32,
        domain_size=262144, full_rows=200770, constant_copy=200692)),
        output=((600,1),), claimed=((22737,1),),
        delta=binding.combine(((600,1),), ((22737,1),), -1),
        metadata_sha256='01'*32, role_page_sha256='02'*32, final_page_sha256='03'*32)
    rows = {200766: selected['delta'],
            200767: binding.canonical([(1,1),(22737,-1)]),
            200769: binding.canonical([(0,1),(200692,-1)])}
    extracted = dict(metadata_sha256=selected['metadata_sha256'],
        role_page_sha256=selected['role_page_sha256'], final_page_sha256=selected['final_page_sha256'],
        identity=dict(relation_digest='ab'*32, domain_size=262144, stored_rows=200770),
        selected_rows=[dict(row=index, a=[[column,f'{value:064x}'] for column,value in a], b=[])
                       for index,a in rows.items()])
    return selected, extracted


class StatementPublicHashTests(unittest.TestCase):
    def test_public_binding_is_derived_from_its_own_row(self):
        selected, extracted = fixture()
        with patch.object(public.binding,'_selected',return_value=selected):
            source = public.generate(b'm',b'f',b'l',extracted,{},None)
        self.assertIn('rho 1 = Poseidon.hash6',source)
        self.assertIn('hashRows : Satisfies rho',source)
        self.assertIn('[(1,1)] [(22737,1)]',source)
        self.assertEqual(source.count('#print axioms'),3)

    def test_changed_public_wire_coefficient_missing_row_or_source_page_refused(self):
        for mutation in ('wire','coefficient','missing','page','orientation'):
            selected, extracted = fixture()
            if mutation=='wire':extracted['selected_rows'][1]['a'][0][0]=2
            elif mutation=='coefficient':extracted['selected_rows'][1]['a'][0][1]=f'{2:064x}'
            elif mutation=='missing':extracted['selected_rows'].pop(1)
            elif mutation=='page':extracted['final_page_sha256']='04'*32
            else:
                for term in extracted['selected_rows'][1]['a']:
                    term[1]=f'{(-int(term[1],16))%MODULUS:064x}'
            with patch.object(public.binding,'_selected',return_value=selected):
                with self.assertRaises(RelationError):public.generate(b'm',b'f',b'l',extracted,{},None)

    def test_omitted_public_row_allows_the_intended_wrong_public_value(self):
        selected, extracted = fixture()
        with patch.object(public.binding,'_selected',return_value=selected):
            raw = public.certificates(b'm',b'f',b'l',extracted,{},None)['raw']
        assignment = {0:1,200692:1,1:1,22737:0,600:0}
        def satisfied(row):
            a,b=row
            left=sum(value*assignment.get(column,0) for column,value in a)%MODULUS
            right=sum(value*assignment.get(column,0) for column,value in b)%MODULUS
            return left*left==right*right
        self.assertEqual([index for index,row in raw.items() if not satisfied(row)],[200767])
        self.assertTrue(all(satisfied(row) for index,row in raw.items() if index!=200767))
        self.assertNotEqual(assignment[1],assignment[22737])


if __name__=='__main__':unittest.main()
