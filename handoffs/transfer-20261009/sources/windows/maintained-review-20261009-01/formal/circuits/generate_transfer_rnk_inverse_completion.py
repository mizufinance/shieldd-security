"""Bounded reciprocal completion after the same-assignment native RNK loop.

The caller supplies independent legality of the selected native input point.
The same accepted SDK scalar supplies positivity and its canonical bound.
The generated constructor derives its reciprocal and prior-row satisfaction;
neither is an application premise. No stream or prover is launched here.
"""
from . import transfer_rnk_inverse_completion as selection
from .generate_transfer_rnk_sparse_sequence import _native_variables, _native_contracts, _row_literal
from .generate_transfer_ivk_reduction_join import _qualify


def generate(checked, extracted, sequence):
    plan = selection.plan(checked, extracted, sequence)
    r = plan['roles']; writes = plan['writes']
    block_names = [f'RuntimeRnkSparseBlock{index:03d}' for index in range(134)]
    chunks = [f'RuntimeRnkNativeChunk{start:03d}' for start in range(0, 126, 16)]
    footprint_name = 'RuntimeRnkInverseFootprint'
    footprint = 'import ShielddSecurity.RuntimeRnkNativeCompletion\n'
    footprint += 'set_option maxHeartbeats 400000\nset_option maxRecDepth 4096\n'
    footprint += f'namespace ShielddSecurity.{footprint_name}\n'
    footprint += f'def writes : List Nat := {writes}\n'
    for index, block in enumerate(block_names):
        footprint += f'''private theorem block{index}_outside : ∀ row ∈ {block}.actualRows,
    ∀ term ∈ row.a ++ row.b, term.1 ∉ writes := by
  have checked : {block}.actualRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∉ writes))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
'''
    footprint += '''theorem original_rows_outside : ∀ row ∈ RuntimeRnkNativeCompletion.actualRows,
    ∀ term ∈ row.a ++ row.b, term.1 ∉ writes := by
  intro row member term present
  simp only [RuntimeRnkNativeCompletion.actualRows,List.mem_append] at member
  rcases member with ''' + ' | '.join('inside' for _ in chunks) + '\n'
    for start, chunk in zip(range(0, 126, 16), chunks):
        indices = [index for index, role in enumerate(sequence['roles']) if role['chunk'] == start]
        footprint += f'''  · obtain ⟨block,included,member⟩ := List.mem_flatten.mp inside
    simp only [{chunk}.rowBlocks,List.mem_cons,List.not_mem_nil,or_false] at included
    rcases included with ''' + ' | '.join('rfl' for _ in indices) + '\n'
        footprint += ''.join(f'    · exact block{index}_outside row member term present\n' for index in indices)
    footprint += '#print axioms original_rows_outside\n'
    footprint = _qualify(footprint + f'end ShielddSecurity.{footprint_name}\n', {})

    name = 'RuntimeRnkNativeInverseCompletion'
    aliases = dict(A='RuntimeRnkSparseAssignment', H='RuntimeRnkNativeCompletion',
        C='RuntimeRnkNativeSource', M='GroupRnkSparseColumns',
        N='RuntimeOwnershipNativeConstructor', SC='ShielddPointCoordinateSeed',
        P=footprint_name)
    source = 'import ShielddSecurity.RuntimeRnkInverseFootprint\n'
    source += 'import ShielddSecurity.GroupNativeSubgroupMultiply\n'
    source += 'set_option maxHeartbeats 400000\nset_option maxRecDepth 4096\n'
    source += f'namespace ShielddSecurity.{name}\n'
    source += ''.join(f'namespace {key} := {value}\n' for key, value in aliases.items())
    source += 'def rawRows : List Row := ' + _row_literal(plan['rows']) + '\n'
    source += f'def originalRows : List Nat := {[row["row"] for row in plan["rows"]]}\n'
    source += _native_variables() + _native_contracts(r['copy'])
    args = 'fq fr model upstream backend codec nk x y input scalar base'
    source += f'''def values (column : Nat) : F :=
  if column = {r['inverse']} then (A.completed {args} {r['x']})⁻¹
  else if column = {r['product']} then 1
  else if column = {r['auxiliary']} then
    ((A.completed {args} {r['x']})⁻¹ - A.completed {args} {r['x']})^2
  else A.completed {args} column
def completed : Nat → F := patchAssignment (A.completed {args}) (values {args}) P.writes
theorem preserves (column : Nat) (outside : column ∉ P.writes) :
    completed {args} column = A.completed {args} column :=
  patchAssignment_preserves _ _ _ column outside
'''
    source += f'''include arithmetic initialHash square primitives one linked accepted in
private theorem constants : A.completed {args} 0 = 1 ∧ A.completed {args} {r['copy']} = 1 := by
  have outside (column : Nat) (independent : column < 3009 ∨ 60775 < column) :
      column ∉ A.writeBlocks.flatten.map M.columns := by
    intro member
    obtain ⟨write,present,equal⟩ := List.mem_map.mp member
    have bounds := M.owned_image_bounds write (A.writes_owned write present)
    rw [equal] at bounds
    omega
  have seeded (column : Nat) (away : column ∉ SC.columns 1520 1521) :
      C.initial fq fr model upstream backend input base column = base column :=
    SC.seed_preserves fq fr (RuntimeOwnershipWindow000Point0Cones.coefficientD : F)
      model upstream backend input 1520 1521 base column away
  have before (column : Nat) (member : column ∈ [0,{r['copy']}]) :
      C.nativePrefix fq fr model upstream backend codec nk x y input base column =
        C.initial fq fr model upstream backend input base column :=
    N.ivk_constants fq backend codec nk x y
      (C.initial fq fr model upstream backend input base) column member
  constructor
  · exact (A.protected_columns {args} 0 (outside 0 (by omega))).trans
      ((before 0 (by simp)).trans ((seeded 0 (by decide)).trans one))
  · exact (A.protected_columns {args} {r['copy']} (outside {r['copy']} (by omega))).trans
      ((before {r['copy']} (by simp)).trans ((seeded {r['copy']} (by decide)).trans (linked.trans one)))
'''
    source += '''variable (standardPrime : Nat.Prime Scalar.order)
variable (inputSubgroup : Scalar.order • upstream.embed (upstream.promote input) = 0)
variable (inputNonidentity : upstream.embed (upstream.promote input) ≠ 0)
'''
    contracts = 'arithmetic initialHash square primitives one linked accepted'
    legal = 'standardPrime inputSubgroup inputNonidentity'
    curve = 'four imaginary nonSquare imaginarySquare'
    source += f'''include {contracts} {legal} in
theorem reciprocal (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    A.completed {args} {r['x']} * (A.completed {args} {r['x']})⁻¹ = 1 := by
  have point := A.native_output_coordinates {args} {contracts} {curve}
  have coordinate := congrArg Group.Point.x point
  have bounds := (ShielddViewingKeyAdmission.successful_scalar primitives _ scalar accepted).2
  change A.completed {args} {r['x']} =
    (model.coordinates (fr.integer scalar • upstream.embed (upstream.promote input))).x at coordinate
  rw [coordinate]
  exact GroupNativeSubgroupMultiply.canonical_input_multiple_inverse
    (RuntimeOwnershipWindow000Point0Cones.coefficientD : F) model standardPrime
    (upstream.embed (upstream.promote input)) inputSubgroup inputNonidentity
    (fr.integer scalar) bounds.1 bounds.2
include {contracts} {legal} in
theorem original_inverse_complete (four : (4 : F) ≠ 0) (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (completed {args}) rawRows := by
  let rho := A.completed {args}
  have inverseValue : completed {args} {r['inverse']} = (rho {r['x']})⁻¹ := by
    simp [completed,patchAssignment,P.writes,values,rho]
  have productValue : completed {args} {r['product']} = 1 := by
    simp [completed,patchAssignment,P.writes,values]
  have auxiliaryValue : completed {args} {r['auxiliary']} = ((rho {r['x']})⁻¹-rho {r['x']})^2 := by
    simp [completed,patchAssignment,P.writes,values,rho]
  have xValue : completed {args} {r['x']} = rho {r['x']} := preserves {args} _ (by decide)
  have before := constants {args} {contracts}
  have oneValue : completed {args} 0 = 1 := (preserves {args} 0 (by decide)).trans before.1
  have copyValue : completed {args} {r['copy']} = 1 := (preserves {args} {r['copy']} (by decide)).trans before.2
  have equation : rho {r['x']}*(rho {r['x']})⁻¹ = 1 :=
    reciprocal {args} {contracts} {legal} {curve}
  intro row member
  simp only [rawRows,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simp only [Square,eval,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,add_zero]
    rw [xValue,inverseValue,auxiliaryValue]
    ring
  · simp only [Square,eval,Int.cast_one,Int.cast_ofNat,one_mul,add_zero]
    rw [xValue,inverseValue,productValue,auxiliaryValue]
    calc
      _ = ((rho {r['x']})⁻¹-rho {r['x']})^2+4*(rho {r['x']}*(rho {r['x']})⁻¹) := by ring
      _ = _ := by rw [equation]; ring
  · simp only [Square,eval,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,add_zero]
    rw [productValue,copyValue]
    ring
  · simp only [Square,eval,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,add_zero]
    rw [oneValue,copyValue]
    ring
include {contracts} in
theorem original_window_complete (imaginary : F)
    (nonSquare : Group.NoUnitSquare (RuntimeOwnershipWindow000Point0Cones.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) :
    Satisfies (completed {args}) H.actualRows :=
  patch_preserves_rows _ _ P.writes H.actualRows
    (H.actual_rows_complete {args} {contracts} imaginary nonSquare imaginarySquare)
    P.original_rows_outside
'''
    for export in ('preserves', 'reciprocal', 'original_inverse_complete', 'original_window_complete'):
        source += '#print axioms ' + export + '\n'
    source = _qualify(source + f'end ShielddSecurity.{name}\n', aliases)
    return {footprint_name: footprint, name: source}
