"""Join the captured statement sponge to its actual compiled public column.

The sparse assertion bundle is extracted from the full ordinary stream. Native
field decoding, the semantic meaning of the 64 inputs, and full Transfer
soundness remain separate obligations.
"""
from . import transfer_statement_binding as binding
from . import transfer_arithmetic as arithmetic, transfer_relation as relation
from .generate_hash_round import linear, _signature_audits


def _selection(manifest, first_page, final_page, accepted_roles, parameter_root):
    selected = binding._selected(manifest, first_page, final_page,
                                 accepted_roles, parameter_root)
    if (selected['claimed'] != ((22737, 1),)
            or selected['checked']['metadata']['constant_copy'] != 200692):
        raise relation.RelationError('exact Transfer claimed witness and copy column')
    return selected


def extract(manifest, first_page, final_page, stream, accepted_roles, parameter_root):
    selected = _selection(manifest, first_page, final_page, accepted_roles, parameter_root)
    obj = selected['checked']['metadata']
    copy = obj['constant_copy']
    outlined = binding.canonical((copy if column == 0 else column, coefficient)
                                 for column, coefficient in selected['delta'])
    required = {
        (binding.canonical([(0, 1), (copy, -1)]), ()): ['constant-copy'],
        (outlined, ()): ['computed-minus-claimed'],
        (binding.canonical([(1, 1), (22737, -1)]), ()): ['public-minus-claimed'],
    }
    result = arithmetic.extract_templates(stream, obj['relation_digest'],
        obj['domain_size'], obj['full_rows'], required, [], [],
        label='statement-computed-and-public-assertions')
    result.update(metadata_sha256=selected['metadata_sha256'],
                  role_page_sha256=selected['role_page_sha256'],
                  final_page_sha256=selected['final_page_sha256'])
    certificates(manifest, first_page, final_page, result, accepted_roles, parameter_root)
    return result


def certificates(manifest, first_page, final_page, extracted, accepted_roles, parameter_root):
    selected = _selection(manifest, first_page, final_page, accepted_roles, parameter_root)
    if (not isinstance(extracted, dict)
            or any(extracted.get(key) != selected[key]
                   for key in ('role_page_sha256', 'final_page_sha256'))):
        raise relation.RelationError('exact statement source pages')
    raw, rows = arithmetic.normalize_selection(extracted,
        selected['checked']['metadata'], selected['metadata_sha256'])
    if set(raw) != {200766, 200767, 200769}:
        raise relation.RelationError('exact three compiled statement/public/copy rows')
    expected = {
        200766: (selected['delta'], ()),
        200767: (binding.canonical([(1, 1), (22737, -1)]), ()),
        200769: (binding.canonical([(0, 1), (200692, -1)]), ()),
    }
    for index, row in expected.items():
        actual = raw[index] if index == 200769 else rows[index]
        if actual != row:
            raise relation.RelationError('exact compiled statement assertion operands')
    selected['raw'] = raw
    return selected


def generate(manifest, first_page, final_page, extracted, accepted_roles, parameter_root):
    selected = certificates(manifest, first_page, final_page,
                            extracted, accepted_roles, parameter_root)
    layout = 'RuntimeTransferStatementHashDomain34Layout'
    module = 'RuntimeTransferStatementPublicHash'
    rows = ',\n'.join('⟨' + linear(a) + ',' + linear(b) + '⟩'
                      for _, (a, b) in sorted(selected['raw'].items()))
    source = f'''import ShielddSecurity.RuntimeTransferStatementHashDomain34Completion
import ShielddSecurity.Compiler
set_option maxHeartbeats 300000
namespace ShielddSecurity.{module}
def originalRows : List Nat := [200766, 200767, 200769]
def rawRows : List Row := [{rows}]
def rows : List Row := Compiler.unoutlineRows 200692 rawRows
theorem constantLink : Compiler.checkRow {layout}.modulus rawRows
    ⟨[(0,1),(200692,-1)],[]⟩ = true := by decide
theorem computed_equals_claimed {{F : Type}} [Field F] [CharP F {layout}.modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rawRows) :
    eval rho {layout}.output = rho 22737 := by
  have normalized := Compiler.unoutline_rows_sound rho 200692 rawRows satisfied constantLink
  have result := Compiler.checked_assertion_sound rho rows {layout}.output [(22737,1)]
    normalized (by decide)
  simpa only [eval, Int.cast_one, one_mul, add_zero] using result
theorem actual_public_hash {{F : Type}} [Field F] [CharP F {layout}.modulus]
    (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho rawRows)
    (hashRows : Satisfies rho {layout}.rawRows) :
    rho 1 = Poseidon.hash6
      (Poseidon.castParameters RuntimeHashBlock_remaining0_statement97_permutation0_0.parameters)
      34 ({layout}.inputs.map (eval rho)) := by
  have normalized := Compiler.unoutline_rows_sound rho 200692 rawRows satisfied constantLink
  have publicRow := Compiler.checked_assertion_sound rho rows [(1,1)] [(22737,1)]
    normalized (by decide)
  have publicEqual : rho 1 = rho 22737 := by
    simpa only [eval, Int.cast_one, one_mul, add_zero] using publicRow
  exact publicEqual.trans ((computed_equals_claimed rho satisfied).symm.trans
    (RuntimeTransferStatementHashDomain34Completion.actual_hash_sound rho one hashRows))
#print axioms constantLink
#print axioms computed_equals_claimed
#print axioms actual_public_hash
end ShielddSecurity.{module}
'''
    return _signature_audits(source)
