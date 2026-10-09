"""Generate exact spend/history slice soundness from selected runtime rows."""
import json
from pathlib import Path
import sys
from generate import P
from spend_rows import select


def name(value):
    return value.replace('.', '_')


def linear(terms):
    return '[' + ', '.join(f'({i}, ({c} : Int))' for i, c in terms) + ']'


def parsed(terms):
    return [(i, int(c, 16) if int(c, 16) <= P // 2 else int(c, 16) - P) for i, c in terms]


def normalized(terms):
    result = {}
    for i, c in terms:
        result[i] = (result.get(i, 0) + c) % P
    return [(i, c if c <= P // 2 else c - P) for i, c in sorted(result.items()) if c]


def completion(selected):
    """A tail extension preserves existing hash/Merkle/public assignments.

    Input range blocks are deliberately prior-stage obligations: in particular,
    the actual position bits are consumed by the Merkle gadget and cannot be
    silently overwritten after its witnesses have been constructed.
    """
    observations, groups, gates = selected['observations'], selected['bits'], selected['gates']

    def col(role):
        terms = observations[role]['linear']
        if len(terms) != 1 or terms[0][1] != 1:
            raise ValueError('extension expected a source witness')
        return terms[0][0]

    borrows = [col(f'spend{s}.borrow') for s in [0, 1]]
    differences = [col(f'spend{s}.difference') for s in [0, 1]]
    # These concrete groups are contiguous in the actual constructor. Unknown
    # allocation shapes require an explicit generator change, not a fallback.
    for s in [0, 1]:
        bits = groups[f'spend{s}.difference']
        if bits != list(range(bits[0], bits[0] + 48)):
            raise ValueError('unsupported difference bit allocation')

    def expression(terms):
        parts = []
        for column, coefficient in terms:
            value = f'(base {column})'
            if column in borrows:
                value = f'(if position{borrows.index(column)} < floor then (1 : F) else 0)'
            parts.append(f'({coefficient} : F) * {value}')
        return ' + '.join(parts) or '(0 : F)'

    prior_blocks = ['constant'] + [f'spend{s}.{role}' for s in [0, 1]
                                  for role in ['amount', 'position', 'floor']]
    fresh = selected['extension_columns']
    out = [f'''
/-- Owned tail auxiliaries only. Input bits, statement slots, opaque hash/root
supports, public and committed columns are all outside this list. -/
def extensionColumns : List Nat := {fresh}
def priorBlocks : List (List Row) := [{', '.join(name(b)+'Rows' for b in prior_blocks)}]
def priorRows : List Row := priorBlocks.flatten
theorem priorDisjoint : priorRows.all (fun row =>
    (row.a ++ row.b).all (fun term => decide (term.1 ∉ extensionColumns))) = true := by decide

def extensionValues {{F : Type}} [Field F] (base : Nat → F)
    (position0 position1 floor column : Nat) : F :=
''']
    for s in [0, 1]:
        out.append(f'  if column = {borrows[s]} then (if position{s} < floor then 1 else 0) else\n')
        out.append(f'  if column = {differences[s]} then (differenceNat (2^48) floor position{s} : F) else\n')
    for s in [0, 1]:
        start = groups[f'spend{s}.difference'][0]
        out.append(f'''  if {start} ≤ column ∧ column < {start+48} then
    (if (encodeBits 48 (differenceNat (2^48) floor position{s}))[column - {start}]?.getD false then 1 else 0) else
''')
    for gate in gates.values():
        x, y = expression(gate['x']), expression(gate['y'])
        out.append(f"  if column = {gate['difference']} then (({x}) - ({y}))^2 else\n")
        out.append(f"  if column = {gate['output']} then ({x}) * ({y}) else\n")
    out.append('  base column\n')
    out.append('''
def extendSpend {F : Type} [Field F] (base : Nat → F)
    (position0 position1 floor : Nat) : Nat → F :=
  patchAssignment base (extensionValues base position0 position1 floor) extensionColumns

theorem extendSpend_preserves {F : Type} [Field F] (base : Nat → F)
    (position0 position1 floor column : Nat) (outside : column ∉ extensionColumns) :
    extendSpend base position0 position1 floor column = base column := by
  exact patchAssignment_preserves _ _ _ _ outside

theorem extendSpend_prior {F : Type} [Field F] (base : Nat → F)
    (position0 position1 floor : Nat) (prior : Satisfies base priorRows) :
    Satisfies (extendSpend base position0 position1 floor) priorRows := by
  exact patch_preserves_rows_checked base _ extensionColumns priorRows prior priorDisjoint
''')
    for s in [0, 1]:
        start = groups[f'spend{s}.difference'][0]
        bitname = f'spend{s}_differenceBits'
        out.append(f'''
theorem extendSpend_difference{s}_map {{F : Type}} [Field F] (base : Nat → F)
    (position0 position1 floor : Nat) :
    {bitname}.map (extendSpend base position0 position1 floor) =
      (encodeBits 48 (differenceNat (2^48) floor position{s})).map
        (fun b => if b then (1 : F) else 0) := by
  have shape : {bitname} = List.range' {start} 48 := by decide
  rw [shape]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have bound : i < 48 := by simpa using hj
    simp only [List.getElem_map, List.getElem_range', Nat.mul_one, Nat.one_mul]
    have member : {start} + i ∈ extensionColumns := by
      have included : (List.range' {start} 48).all
          (fun c => decide (c ∈ extensionColumns)) = true := by decide
      exact of_decide_eq_true ((List.all_eq_true.mp included) ({start}+i)
        (by simp [List.mem_range'] <;> omega))
''')
        for column in borrows + differences:
            out.append(f'    have neq_{column} : {start} + i ≠ {column} := by omega\n')
        if s == 1:
            first = groups['spend0.difference'][0]
            out.append(f'    have earlier : ¬ ({first} ≤ {start}+i ∧ {start}+i < {first+48}) := by omega\n')
        out.append(f'''    have lower : {start} ≤ {start}+i := by omega
    have upper : {start}+i < {start+48} := by omega
    have index : {start}+i-{start} = i := by omega
    simp only [extendSpend, patchAssignment, member, ↓reduceIte,
      extensionValues, {', '.join('neq_'+str(c) for c in borrows+differences)},
      {('earlier, ' if s else '')}lower, upper, and_self, index,
      List.getElem?_eq_getElem (by simpa using bound : i < (encodeBits 48 (differenceNat (2^48) floor position{s})).length),
      Option.getD_some]

theorem extendSpend_difference{s}_complete {{F : Type}} [Field F] (base : Nat → F)
    (position0 position1 floor : Nat) (positionBound : position{s} < 2^48)
    (floorBound : floor < 2^48) :
    Satisfies (extendSpend base position0 position1 floor) spend{s}_differenceRows := by
  have shape : spend{s}_differenceRows = {bitname}.map booleanRow ++
      [reconstructionRow {differences[s]} {bitname}] := by decide
  rw [shape]
  apply range_block_complete
  · rw [extendSpend_difference{s}_map]
    exact (range_completeness (F := F) (encodeBits 48 (differenceNat (2^48) floor position{s}))).1
  · rw [extendSpend_difference{s}_map, binary_cast,
      encodeBits_value 48 _ (differenceNat_bound (2^48) floor position{s} floorBound positionBound)]
    simp [extendSpend, patchAssignment, extensionColumns, extensionValues]
''')
    # Complete the selected tail around already constructed input range/hash
    # witnesses. No premise assumes satisfaction of the tail being proved.
    kept = sorted({i for role, observed in observations.items()
                   if role.endswith(('amount', 'position', 'floor', 'history', 'nullifier',
                                     'real_nullifier', 'computed_root', 'synthetic_nullifier', 'anchor', 'dummy'))
                   for i, _ in observed['linear']} | {0, selected['outline']})
    kept = [i for i in kept if i not in fresh]
    opaque = [name(r) for r in selected['opaque_hash_roles']]

    def semantic(slot, role):
        label = f'spend{slot}.{role}'
        if role in ['real_nullifier', 'computed_root', 'synthetic_nullifier']:
            return f'({name(label)} base)'
        return f'(base {col(label)})'

    def spec(slot):
        dummy = '0' if slot == 0 else semantic(1, 'dummy')
        synthetic = '0' if slot == 0 else semantic(1, 'synthetic_nullifier')
        return ('Spend.BranchSpec ' + ' '.join([dummy, semantic(slot, 'history'),
                semantic(slot, 'amount'), semantic(slot, 'nullifier'),
                semantic(slot, 'real_nullifier'), synthetic,
                semantic(slot, 'computed_root'), semantic(slot, 'anchor')]) +
                f' position{slot} floor')

    out.append(f'''
/-- Constructive completion of exactly the selected spend rows, around an
existing assignment to input range bits, hash/root outputs and statement slots.
Additional full-relation rows reading these fresh auxiliaries are NOT covered;
composition requires their own completion or the checked disjoint-support rule. -/
theorem spend_tail_complete {{F : Type}} [Field F] (base : Nat → F)
    (position0 position1 floor : Nat) (one : base 0 = 1)
    (position0Bound : position0 < 2^48) (position1Bound : position1 < 2^48)
    (floorBound : floor < 2^48)
    (position0Meaning : base {col('spend0.position')} = (position0 : F))
    (position1Meaning : base {col('spend1.position')} = (position1 : F))
    (floorMeaning : base {col('spend0.floor')} = (floor : F))
    (prior : Satisfies base priorRows)
    (legal0 : {spec(0)}) (legal1 : {spec(1)}) :
    ∃ rho : Nat → F, Satisfies rho rows ∧
      ∀ column ∉ extensionColumns, rho column = base column := by
  let rho := extendSpend base position0 position1 floor
  have h_prior : Satisfies rho priorRows := extendSpend_prior base position0 position1 floor prior
''')
    for block in prior_blocks:
        n = name(block)
        out.append(f'  have h_{n} := satisfies_block priorBlocks {n}Rows (by simp [priorBlocks]) rho h_prior\n')
    for column in kept:
        out.append(f'  have fixed_{column} : rho {column} = base {column} := extendSpend_preserves base position0 position1 floor {column} (by decide)\n')
    for s in [0, 1]:
        out.append(f'''  have h_spend{s}_difference : Satisfies rho spend{s}_differenceRows :=
    extendSpend_difference{s}_complete base position0 position1 floor position{s}Bound floorBound
  have borrow{s} : rho {borrows[s]} = (if position{s} < floor then 1 else 0) := by
    simp [rho, extendSpend, patchAssignment, extensionColumns, extensionValues]
  have difference{s} : rho {differences[s]} = (differenceNat (2^48) floor position{s} : F) := by
    simp [rho, extendSpend, patchAssignment, extensionColumns, extensionValues]
''')
    for n, gate in gates.items():
        x, y = expression(gate['x']), expression(gate['y'])
        out.append(f'''  have aux_{gate['difference']} : rho {gate['difference']} = (({x})-({y}))^2 := by
    simp [rho, extendSpend, patchAssignment, extensionColumns, extensionValues]
  have aux_{gate['output']} : rho {gate['output']} = ({x})*({y}) := by
    simp [rho, extendSpend, patchAssignment, extensionColumns, extensionValues]
''')
    out.append(f'''  have required := Spend.required_input_sound
    {semantic(0,'history')} {semantic(0,'amount')} {semantic(0,'nullifier')}
    {semantic(0,'real_nullifier')} 0 {semantic(0,'computed_root')} {semantic(0,'anchor')}
    position0 floor legal0
  have optional := Spend.branch_gates_complete
    {semantic(1,'dummy')} {semantic(1,'history')} {semantic(1,'amount')}
    {semantic(1,'nullifier')} {semantic(1,'real_nullifier')} {semantic(1,'synthetic_nullifier')}
    {semantic(1,'computed_root')} {semantic(1,'anchor')} position1 floor legal1
  have constant : base {selected['outline']} = 1 := by
    have baseConstant := satisfies_block priorBlocks constantRows (by simp [priorBlocks]) base prior
    have equal := equality_row_sound constantRows 0 {selected['outline']} base (by decide) baseConstant
    exact equal.symm.trans one
''')
    fixed_simp = ', '.join([f'fixed_{i}' for i in kept] + ['borrow0', 'borrow1', 'difference0', 'difference1'] +
                           [f'aux_{g[k]}' for g in gates.values() for k in ['difference', 'output']])
    for s in [0, 1]:
        history = col(f'spend{s}.history')
        if s == 0:
            hproof = '    rw [required.2.2]\n    split_ifs <;> simp [Square]\n'
        else:
            hproof = '''    rcases legal1 with ⟨_, _, _, hh⟩ | ⟨_, _, _, hh⟩
    · rw [hh]; split_ifs <;> simp [Square]
    · simp [hh, Square]
'''
        out.append(f'''  have history{s}Boolean : Square (base {history}) (base {history}) := by
{hproof}  have h_spend{s}_booleans : Satisfies rho spend{s}_booleansRows := by
    intro row member
    simp only [spend{s}_booleansRows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simp only [eval, Square, borrow{s}]; split_ifs <;> simp
    · simpa [eval, fixed_{history}] using history{s}Boolean
  have h_spend{s}_comparison : Satisfies rho spend{s}_comparisonRows := by
    have shape : spend{s}_comparisonRows = [comparisonRow spend{s}_positionBits spend{s}_floorBits
      {borrows[s]} {differences[s]} (2^48)] := by decide
    rw [shape]
    intro row member
    have same := List.mem_singleton.mp member
    subst row
    apply comparison_row_complete
    rw [reconstruction_row_sound spend{s}_positionRows {col(f'spend{s}.position')}
      spend{s}_positionBits spend{s}_positionReconstruction rho h_spend{s}_position,
      reconstruction_row_sound spend{s}_floorRows {col(f'spend{s}.floor')}
      spend{s}_floorBits spend{s}_floorReconstruction rho h_spend{s}_floor]
    rw [fixed_{col(f'spend{s}.position')}, fixed_{col(f'spend{s}.floor')}, position{s}Meaning,
      floorMeaning, borrow{s}, difference{s}]
    have borrowMeaning : (borrowNat floor position{s} : F) =
        (if position{s} < floor then 1 else 0) := by
      by_cases recent : floor ≤ position{s}
      · simp [borrowNat, recent, Nat.not_lt.mpr recent]
      · have old : position{s} < floor := by omega
        simp [borrowNat, recent, old]
    simpa [borrowMeaning] using differenceNat_equation (F := F) (2^48) floor position{s} floorBound position{s}Bound
''')

    def zero_block(block, lhs, rhs, equality, target):
        actual = parsed(selected['blocks'][block][0]['a'])
        wanted = normalized(target)
        sign = '' if actual == wanted else '-'
        if sign and actual != normalized([(i, -c) for i, c in wanted]):
            raise ValueError('unknown completeness zero-row sign')
        n = name(block)
        return f'''  have h_{n} : Satisfies rho {n}Rows := by
    intro row member
    have same : row = {n}Rows[0] := by simpa [{n}Rows] using member
    subst row
    have zero : eval rho {linear(actual)} = 0 := by
      calc
        _ = {sign}(({lhs}) - ({rhs})) := by
          simp only [{n}Rows, eval, {fixed_simp}, {', '.join(opaque)}] <;> ring
        _ = 0 := by rw [{equality}] <;> simp
    change Square (eval rho {linear(actual)}) 0
    rw [zero]
    simp only [Square, zero_mul]
'''
    for block, lhs, rhs, eq, target in [
        ('required.nullifier', semantic(0,'nullifier'), semantic(0,'real_nullifier'), 'required.1',
         list(observations['spend0.nullifier']['linear']) + [(i,-c) for i,c in observations['spend0.real_nullifier']['linear']]),
        ('required.anchor', semantic(0,'computed_root'), semantic(0,'anchor'), 'required.2.1',
         list(observations['spend0.computed_root']['linear']) + [(i,-c) for i,c in observations['spend0.anchor']['linear']]),
        ('required.history', semantic(0,'history'), '(if position0 < floor then (1 : F) else 0)', 'required.2.2',
         list(observations['spend0.history']['linear']) + [(borrows[0],-1)]),
    ]:
        out.append(zero_block(block,lhs,rhs,eq,target))
    out.append(f'''  have h_optional_boolean : Satisfies rho optional_booleanRows := by
    intro row member
    have same : row = booleanRow {col('spend1.dummy')} := by simpa [optional_booleanRows, booleanRow] using member
    subst row
    simpa [booleanRow, eval, fixed_{col('spend1.dummy')}] using optional.1
''')
    for n, gate in gates.items():
        x, y, result = [expression(gate[k]) for k in ['x','y','result']]
        normalized_name = name(n)
        derivation = {
            'optional.nullifier': f'''    calc
      _ = {semantic(1,'dummy')} * ({semantic(1,'synthetic_nullifier')} - {semantic(1,'real_nullifier')}) := by
        simp only [{', '.join(opaque)} , eval] <;> ring
      _ = {semantic(1,'nullifier')} - {semantic(1,'real_nullifier')} := by rw [optional.2.1]; ring
      _ = _ := by simp only [{', '.join(opaque)}, eval] <;> ring''',
            'optional.anchor': f'''    convert optional.2.2.1 using 1 <;> simp only [constant, {', '.join(opaque)}, eval] <;> ring''',
            'optional.amount': '    simpa using optional.2.2.2.1',
            'optional.history': '    simpa [constant, sub_eq_add_neg] using optional.2.2.2.2.symm',
        }[n]
        actual = parsed(selected['blocks'][n][2]['a'])
        wanted = normalized([(gate['output'],1)]+[(i,-c) for i,c in gate['result']])
        sign = '' if actual == wanted else '-'
        out.append(f'''  have equation_{normalized_name} : ({x}) * ({y}) = ({result}) := by
{derivation}
  have h_{normalized_name} : Satisfies rho {normalized_name}Rows := by
    intro row member
    simp only [{normalized_name}Rows, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · simp only [eval, Square, {fixed_simp}] <;> ring
    · simp only [eval, Square, {fixed_simp}] <;> ring
    · have zero : eval rho {linear(actual)} = 0 := by
        calc
          _ = {sign}((({x}) * ({y})) - ({result})) := by
            simp only [{normalized_name}Rows, eval, {fixed_simp}] <;> ring
          _ = 0 := by rw [equation_{normalized_name}] <;> simp
      change Square (eval rho {linear(actual)}) 0
      rw [zero]
      simp only [Square, zero_mul]
''')
    out.append('''  refine ⟨rho, ?_, ?_⟩
  · intro row member
    obtain ⟨block, present, rowPresent⟩ := List.mem_flatten.mp member
    simp only [blocks, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with ''' + ' | '.join('rfl' for _ in selected['blocks']) + '\n')
    for block in selected['blocks']:
        out.append(f'    · exact h_{name(block)} row rowPresent\n')
    out.append('''  · intro column outside
    exact extendSpend_preserves base position0 position1 floor column outside

#print axioms spend_tail_complete
#print axioms extendSpend_preserves
#print axioms extendSpend_prior
#print axioms extendSpend_difference0_complete
#print axioms extendSpend_difference1_complete
''')
    return ''.join(out)


def generate(export):
    selected = select(export)
    observations, blocks, groups = selected['observations'], selected['blocks'], selected['bits']

    def lc(role):
        return observations[role]['linear']

    def col(role):
        value = lc(role)
        if len(value) != 1 or value[0][1] != 1:
            raise ValueError('expected private value column')
        return value[0][0]

    def value(role):
        if role.endswith(('real_nullifier', 'computed_root', 'synthetic_nullifier')):
            return f'({name(role)} rho)'
        return f'(rho {col(role)})'

    out = [f'''-- GENERATED from exact actual Transfer rows; do not edit.
-- Full relation digest: {selected['digest']}
import ShielddSecurity.Rows
import ShielddSecurity.Spend
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
namespace ShielddSecurity.RuntimeSpend
def modulus : Nat := {P}
''']
    expression_defs = []
    for role, observed in observations.items():
        if role.endswith(('real_nullifier', 'computed_root', 'synthetic_nullifier')):
            definition = name(role)
            expression_defs.append(definition)
            out.append(f'def {definition} {{F : Type}} [Field F] (rho : Nat → F) : F := eval rho {linear(observed["linear"])}\n')
    unfolding = ', '.join(expression_defs)
    for block, rows in blocks.items():
        rendered = ',\n  '.join('⟨' + linear(parsed(row['a'])) + ', ' + linear(parsed(row['b'])) + '⟩' for row in rows)
        out.append(f'def {name(block)}Rows : List Row := [\n  {rendered}\n]\n')
    for role, bits in groups.items():
        n = name(role)
        out.append(f'''def {n}Bits : List Nat := {bits}
theorem {n}Boolean : {n}Bits.all (fun i => decide (booleanRow i ∈ {n}Rows)) = true := by decide
theorem {n}Reconstruction : reconstructionRow {col(role)} {n}Bits ∈ {n}Rows := by decide
''')
    out.append(f'def blocks : List (List Row) := [{", ".join(name(b) + "Rows" for b in blocks)}]\ndef rows : List Row := blocks.flatten\n')

    def zero_proof(block, index, lhs, rhs, target, indent='  '):
        n = name(block)
        row_a = parsed(blocks[block][index]['a'])
        wanted = normalized(target)
        if row_a == wanted:
            signed = ''
        elif row_a == normalized([(i, -c) for i, c in wanted]):
            signed = '-'
        else:
            raise ValueError(f'{block}: requested equation differs from selected row')
        return f'''{indent}have zero := square_zero _ (h ({n}Rows[{index}]) (List.getElem_mem (by decide : {index} < {n}Rows.length)))
{indent}apply sub_eq_zero.mp
{indent}calc
{indent}  ({lhs}) - ({rhs}) = {signed}(eval rho ({n}Rows[{index}]).a) := by
{indent}    simp [{n}Rows, eval, {unfolding}] <;> ring
{indent}  _ = 0 := by rw [zero] <;> simp
'''

    for block, lhs, rhs, target in [
        ('required.nullifier', value('spend0.nullifier'), value('spend0.real_nullifier'),
         list(lc('spend0.nullifier')) + [(i, -c) for i, c in lc('spend0.real_nullifier')]),
        ('required.anchor', value('spend0.computed_root'), value('spend0.anchor'),
         list(lc('spend0.computed_root')) + [(i, -c) for i, c in lc('spend0.anchor')]),
        ('required.history', value('spend0.history'), value('spend0.borrow'),
         list(lc('spend0.history')) + [(i, -c) for i, c in lc('spend0.borrow')]),
    ]:
        out.append(f'''theorem {name(block)}_sound {{F : Type}} [Field F] (rho : Nat → F)
    (h : Satisfies rho {name(block)}Rows) : {lhs} = {rhs} := by
''' + zero_proof(block, 0, lhs, rhs, target))

    for block, gate in selected['gates'].items():
        n = name(block)
        x, y, result = [f'(eval rho {linear(gate[key])})' for key in ['x', 'y', 'result']]
        d, o = gate['difference'], gate['output']
        out.append(f'''theorem {n}_sound {{F : Type}} [Field F] (rho : Nat → F)
    (four : (4 : F) ≠ 0) (h : Satisfies rho {n}Rows) : {x} * {y} = {result} := by
  have minus := h ({n}Rows[0]) (List.getElem_mem (by decide : 0 < {n}Rows.length))
  have plus := h ({n}Rows[1]) (List.getElem_mem (by decide : 1 < {n}Rows.length))
  have minusA : eval rho ({n}Rows[0]).a = {x} - {y} := by simp [{n}Rows, eval] <;> ring
  have minusB : eval rho ({n}Rows[0]).b = rho {d} := by simp [{n}Rows, eval]
  have plusA : eval rho ({n}Rows[1]).a = {x} + {y} := by simp [{n}Rows, eval] <;> ring
  have plusB : eval rho ({n}Rows[1]).b = rho {d} + 4 * rho {o} := by simp [{n}Rows, eval] <;> ring
  rw [minusA, minusB] at minus
  rw [plusA, plusB] at plus
  have linked : rho {o} = {result} := by
''' + zero_proof(block, 2, f'rho {o}', result,
                [(o, 1)] + [(i, -c) for i, c in gate['result']], '    ') + f'''
  exact (product_encoding _ _ _ _ four minus plus).trans linked
''')

    for slot in [0, 1]:
        s = f'spend{slot}'
        borrow, difference = col(s + '.borrow'), col(s + '.difference')
        history, amount, nf = [value(s + '.' + r) for r in ['history', 'amount', 'nullifier']]
        real_nf, root, anchor = [value(s + '.' + r) for r in ['real_nullifier', 'computed_root', 'anchor']]
        synthetic = '0' if slot == 0 else value(s + '.synthetic_nullifier')
        dummy = '0' if slot == 0 else value('spend1.dummy')
        out.append(f'''theorem {s}Comparison : comparisonRow {s}_positionBits {s}_floorBits
    {borrow} {difference} (2^48) ∈ {s}_comparisonRows := by decide

/-- Arbitrary satisfying assignments obey the required/optional spend branch
and unconditional integer bounds. Hash/root-output meanings are excluded.
The exact caller statement aliases are checked by the source observer bridge. -/
theorem {s}_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (one : rho 0 = 1) (satisfied : Satisfies rho rows) :
    ∃ a position floor : Nat, a < 2^128 ∧ position < 2^48 ∧ floor < 2^48 ∧
      (a : F) = {amount} ∧ (position : F) = {value(s+'.position')} ∧
      (floor : F) = {value(s+'.floor')} ∧
      Spend.BranchSpec {dummy} {history} {amount} {nf} {real_nf} {synthetic}
        {root} {anchor} position floor := by
  have capacity : 2 * 2^48 ≤ modulus := by decide
  have four : (4 : F) ≠ 0 := by
    intro zero
    have impossible : (4 : Nat) = 0 := bounded_cast_injective (F := F) (p := modulus)
      (by decide) (by decide) (by simpa using zero)
    omega
''')
        needed = [b for b in blocks if b.startswith(s + '.') or b == 'constant'
                  or b.startswith('required.' if slot == 0 else 'optional.')]
        for block in needed:
            n = name(block)
            out.append(f'  have h_{n} := satisfies_block blocks {n}Rows (by simp [blocks]) rho satisfied\n')
        for role, integer, bound in [('amount', 'a', 128), ('position', 'position', 48), ('floor', 'floor', 48), ('difference', 'difference', 48)]:
            n = s + '_' + role
            out.append(f'''  obtain ⟨{integer}, bound_{role}, cast_{role}⟩ :
      ∃ n : Nat, n < 2^{bound} ∧ (n : F) = {value(s+'.'+role)} := by
    simpa [{n}Bits] using rows_range_sound {n}Rows {col(s+'.'+role)} {n}Bits {n}Boolean {n}Reconstruction rho h_{n}
''')
        out.append(f'''  have oldBoolean : Square (rho {borrow}) (rho {borrow}) := by
    have h := h_{s}_booleans (booleanRow {borrow}) (by decide)
    simpa [booleanRow, eval] using h
  have equation := comparison_row_sound {s}_comparisonRows {s}_positionBits {s}_floorBits
    {borrow} {difference} (2^48) {s}Comparison rho h_{s}_comparison
  rw [reconstruction_row_sound {s}_positionRows {col(s+'.position')} {s}_positionBits {s}_positionReconstruction rho h_{s}_position,
    reconstruction_row_sound {s}_floorRows {col(s+'.floor')} {s}_floorBits {s}_floorReconstruction rho h_{s}_floor] at equation
  have liftedEquation : (position : F) - (floor : F) =
      (difference : F) - rho {borrow} * (2^48 : Nat) := by
    simpa [cast_position, cast_floor, cast_difference] using equation
  refine ⟨a, position, floor, bound_amount, bound_position, bound_floor,
    cast_amount, cast_position, cast_floor, ?_⟩
''')
        if slot == 0:
            out.append(f'''  apply Spend.bounded_branch_sound (F := F) (p := modulus) (bound := 2^48)
    0 {history} {amount} {nf} {real_nf} 0 {root} {anchor} (rho {borrow})
    capacity bound_position bound_floor bound_difference
  · simp [Square]
  · exact oldBoolean
  · simpa using required_nullifier_sound rho h_required_nullifier
  · simpa [sub_eq_zero] using required_anchor_sound rho h_required_anchor
  · simp
  · simpa using required_history_sound rho h_required_history
  · exact liftedEquation
''')
        else:
            outline = selected['outline']
            out.append(f'''  have constant : rho {outline} = 1 := by
    have linked := equality_row_sound constantRows 0 {outline} (rho := rho) (by decide) h_constant
    simpa [one] using linked.symm
  have dummyBoolean : Square {dummy} {dummy} := by
    have h := h_optional_boolean (booleanRow {col('spend1.dummy')}) (by decide)
    simpa [booleanRow, eval] using h
  have selectedProduct : {dummy} * ({synthetic} - {real_nf}) = {nf} - {real_nf} := by
    convert optional_nullifier_sound rho four h_optional_nullifier using 1 <;>
      simp only [eval, {unfolding}] <;> ring
  have selected : {nf} = {dummy} * {synthetic} + (1 - {dummy}) * {real_nf} := by
    calc
      _ = ({nf} - {real_nf}) + {real_nf} := by ring
      _ = {dummy} * ({synthetic} - {real_nf}) + {real_nf} := by rw [selectedProduct]
      _ = _ := by ring
  have anchorGate : (1 - {dummy}) * ({root} - {anchor}) = 0 := by
    convert optional_anchor_sound rho four h_optional_anchor using 1 <;>
      simp only [eval, {unfolding}, constant] <;> ring
  have amountGate : {dummy} * {amount} = 0 := by
    simpa [eval] using optional_amount_sound rho four h_optional_amount
  have historyGate : {history} = (1 - {dummy}) * (rho {borrow}) := by
    simpa [eval, constant, sub_eq_add_neg] using (optional_history_sound rho four h_optional_history).symm
  exact Spend.bounded_branch_sound (F := F) (p := modulus) (bound := 2^48)
    {dummy} {history} {amount} {nf} {real_nf} {synthetic} {root} {anchor} (rho {borrow})
    capacity bound_position bound_floor bound_difference dummyBoolean oldBoolean
    selected anchorGate amountGate historyGate liftedEquation
''')
        out.append(f'#print axioms {s}_sound\n')
    out.append(completion(selected))
    out.append('end ShielddSecurity.RuntimeSpend\n')
    return '\n'.join(out)


if __name__ == '__main__':
    Path(sys.argv[2]).write_text(generate(json.loads(Path(sys.argv[1]).read_text())), encoding='utf-8')
