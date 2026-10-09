"""Actual folded-product certificates for the two routing word swap choices."""
from . import transfer_relation as relation
from .transfer_fixed_spend import canonical, combine
from .generate_transfer_routing_zero_rows import _lc, _row
from .generate_hash_round import _signature_audits


def generate(extraction):
    if extraction['schema'] != 'shieldd-transfer-routing-tag-rows-v1':
        raise relation.RelationError('actual routing tag derivative required')
    raw = {item['row']: item for item in extraction['selected_rows']}
    link = extraction['plan']['constant_link']
    link_terms = canonical((column, int(value, 16)) for column, value in raw[link]['a'])
    if len(link_terms) != 2 or link_terms[0] != (0, 1) or link_terms[1][1] != relation.MODULUS - 1 or raw[link]['b']:
        raise relation.RelationError('actual constant-copy identity')
    copy = link_terms[1][0]
    words = extraction['plan']['words']
    if len(words) != 2 or words[0]['left'] != words[1]['right'] or words[0]['right'] != words[1]['left']:
        raise relation.RelationError('same two captured sender/receiver hash expressions')
    result = {}
    for slot, word in enumerate(words):
        certificate = word['certificate']
        if len(certificate['rows']) != 2 or canonical(word['swapped']) != canonical(extraction['plan']['flags'][0]):
            raise relation.RelationError('exact physical folded swap product')
        swap, left, right, output, product, auxiliary = map(canonical,
            [word['swapped'], word['left'], word['right'], word['output'], certificate['output'], certificate['auxiliary']])
        if output != combine(right, product):
            raise relation.RelationError('captured swap expression reconstruction')
        difference = combine(left, right, -1)
        expected = [(combine(swap, difference, -1), auxiliary),
                    (combine(swap, difference), combine(canonical((column, coefficient*4)
                       for column, coefficient in product), auxiliary))]
        indices = sorted(set([link, *certificate['rows']]))
        name = f'RuntimeRoutingWordSwap{slot}'
        source = f'''import ShielddSecurity.ScalarBits
import ShielddSecurity.RowOrientationSoundness
set_option maxHeartbeats 400000
namespace ShielddSecurity.{name}
def physicalIndices : List Nat := {indices}
def rawRows : List Row := [
''' + ',\n'.join(_row(raw[index]['a'], raw[index]['b']) for index in indices) + ']\n'
        source += 'def expectedRows : List Row := [\n' + ',\n'.join(_row(a, b) for a, b in expected) + ']\n'
        for identifier, terms in [('swapped', swap), ('left', left), ('right', right),
                                   ('output', output), ('product', product), ('auxiliary', auxiliary)]:
            source += f'def {identifier} : Linear := {_lc(terms)}\n'
        source += f'''variable {{F : Type}} [Field F] [CharP F Scalar.modulus]
theorem swap_equation (rho : Nat → F) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) :
    eval rho output = eval rho right + eval rho swapped * (eval rho left - eval rho right) := by
  have outlined := Compiler.unoutline_rows_sound rho {copy} rawRows satisfied (by decide)
  have normalized := RowOrientationSoundness.checked_rows rho (Compiler.unoutlineRows {copy} rawRows)
    expectedRows (by decide) outlined
  have productValue := Compiler.checked_product_sound rho expectedRows swapped
    (Compiler.subtract left right) product auxiliary four normalized (by decide) (by decide)
  have reconstruction : Compiler.canonical Scalar.modulus output =
      Compiler.canonical Scalar.modulus (right ++ product) := by decide
  rw [Compiler.eval_subtract] at productValue
  rw [Compiler.canonical_equal rho _ _ reconstruction, eval_append, productValue]
theorem selected_word (rho : Nat → F) (four : (4 : F) ≠ 0)
    (satisfied : Satisfies rho rawRows) (swap : Bool)
    (swapValue : eval rho swapped = if swap then 1 else 0) :
    eval rho output = if swap then eval rho left else eval rho right := by
  rw [swap_equation rho four satisfied, swapValue]
  cases swap <;> simp <;> ring
#print axioms swap_equation
#print axioms selected_word
end ShielddSecurity.{name}
'''
        result[name] = _signature_audits(source)
    return result
