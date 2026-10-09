"""First eight actual consecutive remainder steps; no full32/252/508 widening.

Reuses the independently qualified indexed quotient's characteristic lemma.
All selected steps/rows come from the strict complete original remainder view.
"""
from generate_hash_round import linear
from generate_scalar_indexed import indexed_product
from hash_rows import canonical, scaled
from poseidon_graph import P
from scalar_rows import select


def generate(export, parameter_root, export_hash):
    selected = select(export, parameter_root, 'remainder')
    complete = [step for step in selected['steps'] if step['name'] == 'remainder']
    if [step['index'] for step in complete] != list(range(252)):
        raise ValueError('changed original remainder order')
    chosen = complete[:8]
    if len(chosen) != 8 or chosen[0]['before'] != ((0, 1),):
        raise ValueError('changed first original remainder chunk')
    used = {selected['constant_link']}
    for step in chosen:
        used.update(step['certificate'].get('rows', []))
    positions = {original: dense for dense, original in enumerate(sorted(used))}
    out = [f'''import ShielddSecurity.RuntimeScalarIndexedQuotient
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeScalarRemainderChunk0
-- Exact exported source/rows SHA256: {export_hash}
-- Full relation digest (extraction boundary): {export['relation_digest']}
-- Original row indices: {sorted(used)}
-- First8 consecutive original steps only. No canonical reduction/completeness.
def modulus : Nat := {P}
def rawRows : List Row := [
''']
    out.append(',\n'.join('  ⟨' + linear(selected['rows'][i][0]) + ', '
                         + linear(selected['rows'][i][1]) + '⟩' for i in sorted(used)))
    out.append(f''']
def rows : List Row := Compiler.unoutlineRows {selected['outline']} rawRows
theorem constantLink : Compiler.checkRow modulus rawRows
    ⟨[(0, 1), ({selected['outline']}, -1)], []⟩ = true := by
  have indexed : ScalarIndexed.checkRowAt modulus rawRows {positions[selected['constant_link']]}
      ⟨[(0, 1), ({selected['outline']}, -1)], []⟩ = true := by decide
  exact ScalarIndexed.checked_row_membership modulus rawRows {positions[selected['constant_link']]}
    ⟨[(0, 1), ({selected['outline']}, -1)], []⟩ indexed
def indexedSteps : List ScalarIndexed.StepData := [
''')
    records = []
    for step in chosen:
        factor = step['left'] if step['right'] else canonical(((0, 1),) + scaled(step['left'], -1))
        target = canonical(step['after'] + step['left'] + ((0, P - 1),)) if step['right'] else step['after']
        fields = [('before', linear(step['before'])), ('left', linear(step['left'])),
                  ('after', linear(step['after'])), ('right', 'true' if step['right'] else 'false'),
                  ('factor', linear(factor)), ('target', linear(target)),
                  ('product', indexed_product(step['certificate'], positions))]
        records.append('  { ' + ', '.join(f'{key} := {value}' for key, value in fields) + ' }')
    out.append(',\n'.join(records) + '\n]\n')
    out.append(f'''def steps : List ScalarRows.StepData := indexedSteps.map ScalarIndexed.StepData.ordinary
def endpoint : Linear := {linear(chosen[-1]['after'])}
theorem certificate : ScalarRows.checkChain modulus rows [(0, 1)] steps = true := by
  have indexed : ScalarIndexed.checkChain modulus rows [(0, 1)] indexedSteps = true := by decide
  exact ScalarIndexed.checked_chain_membership modulus rows [(0, 1)] indexedSteps indexed

theorem actual_chunk_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rawRows) :
    eval rho endpoint = ScalarRows.polynomialChain rho 1 steps := by
  have normalized : Satisfies rho rows :=
    Compiler.unoutline_rows_sound rho {selected['outline']} rawRows satisfied constantLink
  have recurrence := ScalarRows.checked_chain_sound rho one
    (@RuntimeScalarChains.fourNonzero F _ ‹CharP F modulus›)
    rows normalized [(0, 1)] steps certificate
  have endpointValue : ScalarRows.evaluateChain rho [(0, 1)] steps = eval rho endpoint := by rfl
  rw [endpointValue] at recurrence
  simpa only [eval, one, mul_one, add_zero, Int.cast_one] using recurrence

-- Symbolic append law for later reviewed chunk joins; no wider data check here.
theorem polynomial_append {{F : Type}} [Field F] (rho : Nat → F)
    (value : F) (front back : List ScalarRows.StepData) :
    ScalarRows.polynomialChain rho value (front ++ back) =
      ScalarRows.polynomialChain rho (ScalarRows.polynomialChain rho value front) back := by
  induction front generalizing value with
  | nil => rfl
  | cons step tail ih =>
      simp only [List.cons_append, ScalarRows.polynomialChain]
      exact ih _

#print axioms constantLink
#print axioms certificate
#print axioms actual_chunk_sound
#print axioms polynomial_append
end ShielddSecurity.RuntimeScalarRemainderChunk0
''')
    return ''.join(out)
