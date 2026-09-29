"""Generate exact arithmetic-slice certificates, never a second circuit."""
import json
from pathlib import Path
import sys
from generate import P
from volume_rows import select


def completeness(selected):
    prior, successor, outbound, limit, real, borrow, difference = selected['variables']
    names = ['outbound','prior','successor','candidate','limit','difference']
    groups = dict(zip(names,selected['bits']))
    expressions = dict(zip(names,['b','a','s','(a+b)','l','d']))
    bounds = dict(zip(names,['hb','ha','hs','sumBound','hl','hd']))
    for bits in groups.values():
        if bits != list(range(bits[0],bits[0]+128)):
            raise ValueError('completeness requires actual contiguous bit allocations')
    first,second=sorted([prior,outbound])
    x='(if useReal then (1 : F) else 0)'
    ys={'successor_gate':'((s : F) - ((a+b : Nat) : F))','limit_gate':'((borrowNat (a+b) l : Nat) : F)'}
    clauses=[f'if column = 0 then 1']
    for column,value in [(prior,'(a : F)'),(outbound,'(b : F)'),(successor,'(s : F)'),(limit,'(l : F)'),(real,x),(borrow,ys['limit_gate']),(difference,'(d : F)')]:
        clauses.append(f'else if column = {column} then {value}')
    for name,bits in groups.items():
        start=bits[0]
        clauses.append(f'else if {start} ≤ column ∧ column < {start+128} then if (encodeBits 128 {expressions[name]})[column-{start}]?.getD false then 1 else 0')
    for name,gate in selected['gates'].items():
        clauses.append(f"else if column = {gate['difference']} then ({x} - {ys[name]}) * ({x} - {ys[name]})")
        clauses.append(f"else if column = {gate['output']} then 0")
    clauses.append('else 0')
    lines=[f'''/-- Legal arithmetic inputs extend to every row of the PRECISE arithmetic
slice. This does not assert an extension to unrelated cryptographic family rows.
Padding still requires sumBound, matching unconditional candidate decomposition. -/
theorem volume_input_completeness {{F : Type}} [Field F] [CharP F modulus]
    (a b s l : Nat) (useReal : Bool)
    (ha : a < 2^128) (hb : b < 2^128) (hs : s < 2^128) (hl : l < 2^128)
    (sumBound : a+b < 2^128)
    (tracked : useReal = true → s = a+b ∧ s ≤ l) :
    ∃ rho : Nat → F, rho 0 = 1 ∧ rho {prior} = (a : F) ∧ rho {outbound} = (b : F) ∧
      rho {successor} = (s : F) ∧ rho {limit} = (l : F) ∧
      rho {real} = {x} ∧ Satisfies rho rows := by
  let d := differenceNat (2^128) (a+b) l
  have hd : d < 2^128 := differenceNat_bound (2^128) (a+b) l sumBound hl
  let rho : Nat → F := fun column =>
    {' '.join(clauses)}
''']
    for name,bits in groups.items():
        start=bits[0]
        expression=expressions[name]
        # Prove allocation guards once, rather than asking split_ifs/simp_all to
        # traverse the full assignment and every previously proved row block.
        guards = []
        for column in [0, prior, outbound, successor, limit, real, borrow, difference]:
            guards.append((f'{start}+i ≠ {column}', 'if_neg'))
        for previous, previous_bits in groups.items():
            if previous == name:
                break
            low = previous_bits[0]
            guards.append((f'¬ ({low} ≤ {start}+i ∧ {start}+i < {low+128})', 'if_neg'))
        guards.append((f'{start} ≤ {start}+i ∧ {start}+i < {start+128}', 'if_pos'))
        guard_proofs = '\n'.join(
            f'        have guard{j} : {proposition} := by omega'
            for j, (proposition, _) in enumerate(guards))
        guard_rewrites = ', '.join(
            f'{rewrite} guard{j}' for j, (_, rewrite) in enumerate(guards))
        lines.append(f'''  have map_{name} : {name}Bits.map rho = (encodeBits 128 {expression}).map (fun bit => if bit then (1 : F) else 0) := by
    have columns : {name}Bits = List.range' {start} 128 := by decide
    rw [columns]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have indexBound : i < 128 := by simpa using hi
      have subtract : {start}+i-{start} = i := by omega
      simp only [List.getElem_map, List.getElem_range', Nat.one_mul]
      have atIndex : rho ({start}+i) = (if (encodeBits 128 {expression})[i]?.getD false then (1 : F) else 0) := by
{guard_proofs}
        simp only [rho, {guard_rewrites}, subtract]
      rw [atIndex]
      have valid : i < (encodeBits 128 {expression}).length := by simpa only [encodeBits_length] using indexBound
      rw [List.getElem?_eq_getElem valid]
      rfl
  have binary_{name} : fieldBinary ({name}Bits.map rho) = (({expression} : Nat) : F) := by
    rw [map_{name}, binary_cast, encodeBits_value 128 {expression} {bounds[name]}]
''')
    value_columns={'outbound':outbound,'prior':prior,'successor':successor,'limit':limit,'difference':difference}
    for name,column in value_columns.items():
        lines.append(f'''  have h_{name} : Satisfies rho {name}Rows := by
    have shape : {name}Rows = {name}Bits.map booleanRow ++ [reconstructionRow {column} {name}Bits] := by decide
    rw [shape]
    apply range_block_complete
    · rw [map_{name}]
      exact (range_completeness (F := F) (encodeBits 128 {expressions[name]})).1
    · rw [binary_{name}]
      simp [rho]
''')
    lines.append(f'''  have h_candidate : Satisfies rho candidateRows := by
    have shape : candidateRows = candidateBits.map booleanRow ++ [sumReconstructionRow {first} {second} candidateBits] := by decide
    rw [shape]
    apply sum_block_complete
    · rw [map_candidate]
      exact (range_completeness (F := F) (encodeBits 128 (a+b))).1
    · rw [binary_candidate]
      simp [rho, Nat.cast_add] <;> ring
  have h_comparison : Satisfies rho comparisonRows := by
    have shape : comparisonRows = [comparisonRow limitBits candidateBits {borrow} {difference} (2^128)] := by decide
    rw [shape]
    intro row member
    have same := List.mem_singleton.mp member
    subst row
    apply comparison_row_complete
    rw [binary_limit, binary_candidate]
    simpa [rho, d] using differenceNat_equation (F := F) (2^128) (a+b) l sumBound hl
  have h_booleans : Satisfies rho booleansRows := by
    intro row member
    simp only [booleansRows, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · cases useReal <;> simp [rho, eval, Square]
    · simp only [eval, Square]
      simp [rho, borrowNat]
  have zero_successor_gate : {x} * {ys['successor_gate']} = 0 := by
    cases useReal with
    | false => simp
    | true =>
      have equal := (tracked rfl).1
      simp [equal]
  have zero_limit_gate : {x} * {ys['limit_gate']} = 0 := by
    cases useReal with
    | false => simp
    | true =>
      have condition := tracked rfl
      have within : a+b ≤ l := by omega
      simp [borrowNat, within]
''')
    for name in selected['gates']:
        y=ys[name]
        lines.append(f'''  have h_{name} : Satisfies rho {name}Rows := by
    intro row member
    simp only [{name}Rows, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp [rho, eval, Square, Nat.cast_add] <;> ring
    · unfold Square
      calc
        _ = ({x}+{y}) * ({x}+{y}) := by simp [rho, eval, Nat.cast_add] <;> ring
        _ = ({x}-{y}) * ({x}-{y}) + 4*({x}*{y}) := by ring
        _ = _ := by rw [zero_{name}]; simp [rho, eval, Nat.cast_add] <;> ring
    · simp [rho, eval, Square]
''')
    lines.append('''  refine ⟨rho, by simp [rho], by simp [rho], by simp [rho],
    by simp [rho], by simp [rho], by simp [rho], ?_⟩
  intro row member
  obtain ⟨block, present, rowPresent⟩ := List.mem_flatten.mp member
  simp only [blocks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at present
  rcases present with ''' + ' | '.join('rfl' for _ in selected['blocks']) + '\n')
    for name in selected['blocks']:
        lines.append(f'  · exact h_{name} row rowPresent\n')
    lines.append('#print axioms volume_input_completeness\n')
    return '\n'.join(lines)


def generate(export):
    selected = select(export)
    prior, successor, outbound, limit, real, borrow, difference = selected['variables']
    names = ['outbound','prior','successor','candidate','limit','difference']
    groups = dict(zip(names, selected['bits']))
    if not max(groups['limit']) < min(groups['candidate']) or not max(groups['candidate']) < borrow < difference:
        raise ValueError('unsupported comparator allocation order')
    first, second = sorted([prior, outbound])

    def linear(terms):
        values = [(i,int(c,16)) for i,c in terms]
        return '[' + ', '.join(f'({i}, ({c if c<=P//2 else c-P} : Int))' for i,c in values) + ']'
    def row(value):
        return '⟨' + linear(value['a']) + ', ' + linear(value['b']) + '⟩'
    out = [f'''-- GENERATED from actual Transfer rows; do not edit.
-- Full relation digest: {export['relation_digest']}
import ShielddSecurity.Rows
import ShielddSecurity.Volume
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeVolume
def modulus : Nat := {P}
''']
    for name, rows in selected['blocks'].items():
        out.append(f'def {name}Rows : List Row := [\n  ' + ',\n  '.join(row(r) for r in rows) + '\n]\n')
    for name,bits in groups.items():
        out.append(f'def {name}Bits : List Nat := {bits}\n')
        out.append(f'theorem {name}Boolean : {name}Bits.all (fun i => decide (booleanRow i ∈ {name}Rows)) = true := by decide\n')
    value_columns = dict(zip(['outbound','prior','successor','limit','difference'],[outbound,prior,successor,limit,difference]))
    for name,column in value_columns.items():
        out.append(f'theorem {name}Reconstruction : reconstructionRow {column} {name}Bits ∈ {name}Rows := by decide\n')
    out.append(f'''theorem candidateReconstruction : sumReconstructionRow {first} {second} candidateBits ∈ candidateRows := by decide
theorem comparisonEquation : comparisonRow limitBits candidateBits {borrow} {difference} (2^128) ∈ comparisonRows := by decide
def blocks : List (List Row) := [{', '.join(name+'Rows' for name in selected['blocks'])}]
def rows : List Row := blocks.flatten
''')
    for name, y in [('successor_gate', f'(rho {successor} - rho {prior} - rho {outbound})'),('limit_gate',f'(rho {borrow})')]:
        auxiliary = selected['gates'][name]['difference']
        product = selected['gates'][name]['output']
        out.append(f'''theorem {name}_sound {{F : Type}} [Field F] (rho : Nat → F)
    (four : (4 : F) ≠ 0) (h : Satisfies rho {name}Rows) : rho {real} * {y} = 0 := by
  have minus := h ({name}Rows[0]) (List.getElem_mem (by decide : 0 < {name}Rows.length))
  have plus := h ({name}Rows[1]) (List.getElem_mem (by decide : 1 < {name}Rows.length))
  have minusA : eval rho ({name}Rows[0]).a = rho {real} - {y} := by simp [{name}Rows, eval] <;> ring
  have minusB : eval rho ({name}Rows[0]).b = rho {auxiliary} := by simp [{name}Rows, eval]
  have plusA : eval rho ({name}Rows[1]).a = rho {real} + {y} := by simp [{name}Rows, eval] <;> ring
  have plusB : eval rho ({name}Rows[1]).b = rho {auxiliary} + 4 * rho {product} := by simp [{name}Rows, eval] <;> ring
  rw [minusA, minusB] at minus
  rw [plusA, plusB] at plus
  have zero : rho {product} = 0 := by
    have hrow := square_zero _ (h ({name}Rows[2]) (List.getElem_mem (by decide : 2 < {name}Rows.length)))
    simpa [{name}Rows, eval] using hrow
  exact (product_encoding _ _ _ _ four minus plus).trans zero
''')
    out.append(f'''/-- Exact selected-row implication for arbitrary assignments in the deployed
Transfer layout. Full-relation membership relies on the named exporter boundary. -/
theorem volume_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho rows) :
    ∃ a b s l : Nat,
      a < 2^128 ∧ b < 2^128 ∧ s < 2^128 ∧ l < 2^128 ∧
      (a : F) = rho {prior} ∧ (b : F) = rho {outbound} ∧
      (s : F) = rho {successor} ∧ (l : F) = rho {limit} ∧
      a+b < 2^128 ∧ (rho {real} = 1 → s = a+b ∧ s ≤ l) := by
  have capacity : 2 * 2^128 ≤ modulus := by decide
  have four : (4 : F) ≠ 0 := by
    intro zero
    have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
      (by decide) (by decide) (by simpa using zero)
    omega
''')
    for name in selected['blocks']:
        out.append(f'  have h_{name} := satisfies_block blocks {name}Rows (by simp [blocks]) rho satisfied\n')
    for name,column in value_columns.items():
        out.append(f'''  have r_{name} : AmountRange (2^128) (rho {column}) := by
    simpa [AmountRange, {name}Bits] using rows_range_sound {name}Rows {column} {name}Bits {name}Boolean {name}Reconstruction rho h_{name}
''')
    out.append(f'''  have r_candidate : AmountRange (2^128) (fieldBinary (candidateBits.map rho)) := by
    have result := range_sound (candidateBits.map rho) (fieldBinary (candidateBits.map rho))
      (rows_bits_sound candidateRows candidateBits candidateBoolean rho h_candidate) rfl
    simpa [AmountRange, candidateBits] using result
  have candidateEquation : rho {prior} + rho {outbound} = fieldBinary (candidateBits.map rho) := by
    rw [sum_reconstruction_sound candidateRows {first} {second} candidateBits candidateReconstruction rho h_candidate]
    ring
  have successorGate : rho {real} * (rho {successor} - fieldBinary (candidateBits.map rho)) = 0 := by
    rw [← candidateEquation]
    convert successor_gate_sound rho four h_successor_gate using 1 <;> ring
  have comparison : rho {limit} - fieldBinary (candidateBits.map rho) = rho {difference} - rho {borrow} * (2^128 : Nat) := by
    have result := comparison_row_sound comparisonRows limitBits candidateBits {borrow} {difference} (2^128) comparisonEquation rho h_comparison
    rw [reconstruction_row_sound limitRows {limit} limitBits limitReconstruction rho h_limit] at result
    exact result
  exact volume_arithmetic_sound (F := F) (p := modulus) (2^128) capacity
    (rho {prior}) (rho {outbound}) (rho {successor}) (fieldBinary (candidateBits.map rho))
    (rho {limit}) (rho {difference}) (rho {real}) (rho {borrow})
    ⟨r_prior, r_outbound, r_successor, r_candidate, r_limit, r_difference,
      candidateEquation, successorGate, limit_gate_sound rho four h_limit_gate, comparison⟩
#print axioms volume_sound
''')
    out.append(completeness(selected))
    out.append('end ShielddSecurity.RuntimeVolume\n')
    return '\n'.join(out)


if __name__ == '__main__':
    Path(sys.argv[2]).write_text(generate(json.loads(Path(sys.argv[1]).read_text())),encoding='utf-8')
