"""Symbolic eight-chunk composition of actual 126-window constructors.

The inputs are reaccepted capture metadata and retained actual row selections.
This generator performs no ordinary-stream scan, invents no observations and
supplies no native coordinates or preceding row truth. Native precomputation
and written IVK bit values must be supplied by their owned constructor joins.
"""
from . import generate_transfer_ownership_constructor_candidates as candidates
from . import transfer_ownership_completion as completion
from . import transfer_ownership_constructor_join as joins
from .generate_hash_round import _signature_audits


def _append(values):
    # Lean's ++ is infixl. Keep chunk proofs opaque by choosing an explicit
    # right-associated syntax tree, matching the sequential append lemmas.
    values=list(values)
    result=values[-1]
    for value in reversed(values[:-1]):
        result=value+' ++ ('+result+')'
    return result


def _member(index, count, expression):
    """Membership in a right-associated append of opaque chunk lists."""
    result = expression if index == count-1 else f'List.mem_append_left _ ({expression})'
    for _ in range(index):
        result = f'List.mem_append_right _ ({result})'
    return result


def generate(chunks, selections, readonly_lcs=()):
    candidates.validate_all_chunks(chunks, selections)
    expected = list(range(0, 126, 16))
    if len(chunks) != 8 or [item['metadata']['window_start'] for item in chunks] != expected or \
            [item['metadata']['window_count'] for item in chunks] != [16]*7+[14]:
        raise completion.relation.RelationError('ownership trace exact eight bounded all126 chunks')
    copy = chunks[0]['metadata']['constant_copy']
    frames = []
    for checked, extracted in zip(chunks, selections):
        if checked['metadata']['schema'] != 'shieldd-transfer-ownership-v1':
            raise completion.relation.RelationError('ownership trace exact owned source family')
        before = None
        previous = None
        for offset in range(checked['metadata']['window_count']):
            plan = completion.window_plan(checked, extracted, offset, False, readonly_lcs)
            joins.actual_window_partition(checked, extracted, offset, readonly_lcs)
            low = [column for column in plan['writes'] if column < 22738]
            high = [column for column in plan['writes'] if 22738 <= column < copy]
            if not low or not high or min(low) < 2257 or 3766 in plan['writes'] or copy in plan['writes']:
                raise completion.relation.RelationError('ownership trace protected actual allocation fences')
            current = min(low), min(high)
            if previous is not None and current != previous:
                raise completion.relation.RelationError('ownership trace exact local allocation adjacency')
            if before is None:
                before = current
            previous = max(low)+1, max(high)+1
        if frames and frames[-1][1] != before:
            raise completion.relation.RelationError('ownership trace exact cross-chunk allocation adjacency')
        frames.append((before, previous))
    return _render(copy)


def _render(copy):
    """Pure proof template; callers must retain the complete typed validation.

    This private renderer also supports a proof-only successor of an already
    validated, immutable source packet. It does not accept or qualify metadata.
    """
    if type(copy) is not int or copy <= 22738:
        raise completion.relation.RelationError('ownership trace constant copy column')
    expected = list(range(0, 126, 16))
    names = [f'RuntimeOwnershipConstructorChunk{start:03d}' for start in expected]
    name = 'RuntimeOwnershipConstructorTrace'
    source = ''.join(f'import ShielddSecurity.{chunk}\n' for chunk in names)
    source += '''import ShielddSecurity.GroupCircuitProgramTrace
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
'''
    source += f'namespace ShielddSecurity.{name}\n'
    source += ''.join(f'namespace C{index} := {chunk}\n' for index, chunk in enumerate(names))
    source += '''open GroupFixedCircuitCompletion GroupFixedCircuitBounds
def kept : List Nat := C0.kept
def tables : GroupVariableCircuitCompletion.Tables := C0.tables
def input : Linear × Linear := C0.input
def priorRows : List Row := C0.priorRows
def beforeFrame : Frame := C0.beforeFrame
def afterFrame : Frame := C7.afterFrame
def segments (bits : Nat → Bool) : List (Program × Frame) :=
  '''+_append(f'C{index}.segments bits' for index in range(8))+'''
def programs (bits : Nat → Bool) : List Program :=
  '''+_append(f'C{index}.programs bits' for index in range(8))+'''
def originalRows : List Row :=
  '''+_append(f'C{index}.originalRows' for index in range(8))+'\n'
    for index in range(8):
        source += f'''private theorem frame{index} (bits : Nat → Bool) :
    GroupCircuitFrameTrace.lastFrame C{index}.beforeFrame (C{index}.segments bits) = C{index}.afterFrame := by
  rfl
'''
        if index < 7:
            source += f'''private theorem boundary{index} :
    C{index}.afterFrame = C{index+1}.beforeFrame := by
  rfl
'''
            source += f'''private theorem output{index} (bits : Nat → Bool) :
    output C{index}.input (C{index}.programs bits) = C{index+1}.input := by
  rfl
'''
    source += '''private theorem programs_segments (bits : Nat → Bool) :
    (segments bits).map Prod.fst = programs bits := by
  simp only [segments,programs,List.map_append,'''+','.join(f'C{i}.programs' for i in range(8))+''']
theorem certified (bits : Nat → Bool) : Certified 22738 '''+str(copy)+''' beforeFrame (segments bits) := by
  unfold segments beforeFrame
'''
    for index in range(7):
        source += f'''  rw [GroupCircuitFrameTrace.certified_append]
  refine ⟨C{index}.certified bits,?_⟩
  rw [frame{index},boundary{index}]
'''
    source += '''  exact C7.certified bits
theorem aligned (bits : Nat → Bool) : Aligned input (programs bits) := by
  unfold programs input
'''
    for index in range(7):
        source += f'''  rw [GroupCircuitProgramTrace.aligned_append]
  refine ⟨C{index}.aligned bits,?_⟩
  rw [output{index}]
'''
    source += '  exact C7.aligned bits\n'
    branches = ' | '.join('present' for _ in names)
    for export, target, theorem in (
            ('protected_programs', 'Protected kept program', 'protected_programs'),
            ('bit_supports', '∀ term ∈ program.low ++ program.high, term.1 ∈ kept', 'bit_supports')):
        source += f'''theorem {export} (bits : Nat → Bool) : ∀ program ∈ programs bits, {target} := by
  intro program member
  simp only [programs,List.mem_append] at member
  rcases member with {branches}
'''
        source += ''.join(f'  · exact C{i}.{theorem} bits program present\n' for i in range(8))
    source += '''theorem table_supports : ∀ term ∈ tables.terms, term.1 ∈ kept :=
  C0.table_supports
theorem constructors {F : Type} [Field F] [CharP F C0.modulus]
    (imaginary : F) (nonSquare : Group.NoUnitSquare (C0.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (bits : Nat → Bool) :
    ∀ program ∈ programs bits, GroupVariableCircuitCompletion.LocalConstruct
      (C0.coefficientD : F) '''+str(copy)+''' tables program := by
  intro program member
  simp only [programs,List.mem_append] at member
  rcases member with '''+branches+'\n'
    source += ''.join(f'  · exact C{i}.constructors imaginary nonSquare imaginarySquare bits program present\n' for i in range(8))
    source += f'''theorem initial_support : RowsCovered 22738 {copy} beforeFrame priorRows := by
  have checked : priorRows.all (fun row => (row.a ++ row.b).all
      (fun term => decide (covers 22738 {copy} beforeFrame term.1))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
theorem fresh (bits : Nat → Bool) : Fresh priorRows (programs bits) := by
  have result := bounded_fresh 22738 {copy} beforeFrame priorRows (segments bits)
    initial_support (certified bits)
  rw [programs_segments] at result
  exact result
theorem original_rows_covered (bits : Nat → Bool) :
    ∀ row ∈ originalRows, row ∈ priorRows ++ rows (programs bits) := by
  intro row member
  simp only [originalRows,List.mem_append] at member
  have expanded : rows (programs bits) = {_append(f'rows (C{i}.programs bits)' for i in range(8))} := by
    simp only [programs,GroupCircuitProgramTrace.rows_append]
  rcases member with {branches}
'''
    for index in range(8):
        source += f'  · have covered := C{index}.original_rows_covered bits row present\n'
        if index == 0:
            source += '''    rcases List.mem_append.mp covered with earlier | current
    · exact List.mem_append_left _ earlier
    · apply List.mem_append_right
      rw [expanded]
      exact '''+_member(index,8,'current')+'\n'
        else:
            source += f'''    have current : row ∈ rows (C{index}.programs bits) := by
      simpa only [C{index}.priorRows,List.nil_append] using covered
    apply List.mem_append_right
    rw [expanded]
    exact {_member(index,8,'current')}
'''
    source += f'''theorem constructs_from_precompute {{F : Type}} [Field F] [CharP F C0.modulus]
    (imaginary : F) (nonSquare : Group.NoUnitSquare (C0.coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (bits : Nat → Bool) (base : Nat → F)
    (one : base 0 = 1) (linked : base {copy} = base 0)
    (precomputed : Satisfies base priorRows)
    (incoming : Group.OnCurve (C0.coefficientD : F) (point base input))
    (tableCurves : GroupVariableCircuitCompletion.Curved (C0.coefficientD : F) tables base)
    (values : ∀ program ∈ programs bits,
      eval base program.low = (if program.lowBit then 1 else 0) ∧
      eval base program.high = (if program.highBit then 1 else 0)) :
    Satisfies (run base (programs bits)) originalRows ∧
      Group.OnCurve (C0.coefficientD : F)
        (point (run base (programs bits)) (output input (programs bits))) ∧
      GroupVariableCircuitCompletion.Curved (C0.coefficientD : F) tables (run base (programs bits)) ∧
      (∀ column ∈ kept, run base (programs bits) column = base column) := by
  have result := GroupVariableCircuitCompletion.constructs (C0.coefficientD : F) {copy}
    base tables (programs bits) input priorRows kept
    (constructors imaginary nonSquare imaginarySquare bits) (protected_programs bits) table_supports
    (bit_supports bits) (fresh bits) (aligned bits)
    (by exact List.mem_append_left _ (List.mem_range.mpr (by decide)))
    (by exact List.mem_append_right _ (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl))))
    one linked precomputed incoming tableCurves values
  exact ⟨(by intro row member; exact result.1 row (original_rows_covered bits row member)),result.2⟩
'''
    for export in ('certified','aligned','protected_programs','table_supports','bit_supports','constructors',
                   'initial_support','fresh','original_rows_covered','constructs_from_precompute'):
        source += '#print axioms '+export+'\n'
    for index,chunk in enumerate(names):
        source=source.replace(f'namespace C{index} := {chunk}\n','').replace(f'C{index}.',chunk+'.')
    return name, _signature_audits(source+f'end ShielddSecurity.{name}\n')
