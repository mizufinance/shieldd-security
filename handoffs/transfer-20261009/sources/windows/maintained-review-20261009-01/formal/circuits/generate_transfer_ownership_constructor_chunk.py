"""Bounded proof adapters for the symbolic actual variable-base constructor.

Local modules construct their own rows. This renderer composes their exact
finite frames, adjacency, protected source roles and original-row partitions;
it does not invent incoming row truth, Boolean values or native coordinates.
"""
from . import generate_transfer_ownership_constructor_candidates as candidates
from . import transfer_ownership_completion as completion
from . import transfer_ownership_constructor_join as joins
from .generate_hash_round import _signature_audits


def generate(checked, extracted, readonly_lcs=()):
    start,count=candidates._chunk(checked,extracted)
    if checked['metadata']['schema']!='shieldd-transfer-ownership-v1':
        raise completion.relation.RelationError('ownership constructor chunk exact owned source family')
    copy=checked['metadata']['constant_copy'];origin=22738;fence=2257
    observe=lambda value: checked['derived'][value[1]] if value[0]=='source' else completion.canonical([(0,value[1])])
    plans=[];previous=None
    for offset in range(count):
        plan=completion.window_plan(checked,extracted,offset,False,readonly_lcs)
        joins.actual_window_partition(checked,extracted,offset,readonly_lcs)
        low=[column for column in plan['writes'] if column<origin]
        high=[column for column in plan['writes'] if origin<=column<copy]
        if not low or not high or min(low)<fence or 3766 in plan['writes'] or copy in plan['writes']:
            raise completion.relation.RelationError('ownership chunk exact protected low frame/randomizer/copy')
        before=(min(low),min(high));after=(max(low)+1,max(high)+1)
        if previous is not None and previous!=before:
            raise completion.relation.RelationError('ownership chunk consecutive actual allocation fences')
        previous=after
        if offset and checked['windows'][offset][0]!=checked['windows'][offset-1][4]:
            raise completion.relation.RelationError('ownership chunk actual source adjacency')
        low_index=2*(125-start-offset)
        bit_terms=[checked['derived'][handle] for handle in checked['bits'][low_index:low_index+2]]
        if any(column>=fence for terms in bit_terms for column,_ in terms):
            raise completion.relation.RelationError('ownership chunk actual Boolean support fence')
        plans.append(plan)
    table_terms=[observe(value) for role in ('base','twice','triple') for value in checked['points'][role]]
    if any(column>=fence for terms in table_terms for column,_ in terms):
        raise completion.relation.RelationError('ownership chunk exact shared table support fence')
    stems=[f'RuntimeOwnershipWindow{start+offset:03d}' for offset in range(count)]
    programs=[stem+'Program' for stem in stems]
    values=[f'{program}.program (bits {2*(125-start-offset)}) (bits {2*(125-start-offset)+1})'
            for offset,program in enumerate(programs)]
    name=f'RuntimeOwnershipConstructorChunk{start:03d}'
    source=''.join(f'import ShielddSecurity.{program}\n' for program in programs)
    source+='''import ShielddSecurity.GroupCircuitFrameTrace
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
'''
    source+=f'''namespace ShielddSecurity.{name}
open GroupFixedCircuitCompletion GroupFixedCircuitBounds
def modulus : Nat := {completion.relation.MODULUS}
def coefficientD : Int := {(-10240*pow(10241,-1,completion.relation.MODULUS))%completion.relation.MODULUS}
def kept : List Nat := List.range {fence} ++ [3766,{copy}]
def tables : GroupVariableCircuitCompletion.Tables := {programs[0]}.tables
def beforeFrame : Frame := {programs[0]}.beforeFrame
def afterFrame : Frame := {programs[-1]}.afterFrame
def segments (bits : Nat → Bool) : List (Program × Frame) :=
  [{','.join(f'({value},{program}.afterFrame)' for value,program in zip(values,programs))}]
def programs (bits : Nat → Bool) : List Program := (segments bits).map Prod.fst
def input : Linear × Linear := ({programs[0]}.program false false).input
def originalBlocks : List (List Row) := [{','.join(stem+'.rawRows' for stem in stems)}]
def originalRows : List Row := originalBlocks.flatten
def priorRows : List Row := {programs[0]+'.priorRows' if start==0 else '[]'}
'''
    for offset,(program,value) in enumerate(zip(programs,values)):
        before=program+'.beforeFrame'
        source+=f'''private theorem protected{offset} (bits : Nat → Bool) : Protected kept ({value}) := by
  have bounds := checked_local {origin} {copy} {before} {program}.afterFrame
    ({value}) ({program}.checked_bounds _ _)
  have floor : {fence} ≤ {before}.low := by decide
  have randomizer : ({program}.program false false).stages.all
      (fun stage => stage.writes.all (fun column => decide (column ≠ 3766))) = true := by decide
  intro stage member column inside written
  rcases List.mem_append.mp inside with small | named
  · exact bounds.2.2 stage member column written
      (Or.inl (Nat.lt_of_lt_of_le (List.mem_range.mp small) floor))
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at named
    rcases named with rfl | rfl
    · exact of_decide_eq_true
        (List.all_eq_true.mp (List.all_eq_true.mp randomizer stage member) _ written) rfl
    · exact bounds.2.2 stage member {copy} written (Or.inr (Or.inr rfl))
private theorem bits{offset} (bits : Nat → Bool) :
    ∀ term ∈ ({value}).low ++ ({value}).high, term.1 ∈ kept := by
  have checked : (({program}.program false false).low ++ ({program}.program false false).high).all
      (fun term => decide (term.1 < {fence})) = true := by decide
  intro term member
  apply List.mem_append_left
  exact List.mem_range.mpr (of_decide_eq_true (List.all_eq_true.mp checked term member))
'''
    source+='''theorem certified (bits : Nat → Bool) :
    Certified 22738 '''+str(copy)+''' beforeFrame (segments bits) := by
'''
    for offset,(program,value) in enumerate(zip(programs,values)):
        source+=f'''  have head{offset} := checked_local {origin} {copy} {program}.beforeFrame {program}.afterFrame
    ({value}) ({program}.checked_bounds _ _)
  refine ⟨head{offset}.1,head{offset}.2.1,head{offset}.2.2,?_⟩
'''
    source+='  exact True.intro\n'
    source+='''theorem aligned (bits : Nat → Bool) : Aligned input (programs bits) := by
  exact '''+'⟨rfl,'*count+'True.intro'+'⟩'*count+'\n'
    unfold_members='[programs,segments,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false]'
    branches=' | '.join('rfl' for _ in programs)
    source+=f'''theorem protected_programs (bits : Nat → Bool) : ∀ program ∈ programs bits, Protected kept program := by
  intro program member
  simp only {unfold_members} at member
  rcases member with {branches}
'''
    source+=''.join(f'  · exact protected{offset} bits\n' for offset in range(count))
    source+=f'''theorem table_supports : ∀ term ∈ tables.terms, term.1 ∈ kept := by
  have checked : tables.terms.all (fun term => decide (term.1 < {fence})) = true := by decide
  intro term member
  apply List.mem_append_left
  exact List.mem_range.mpr (of_decide_eq_true (List.all_eq_true.mp checked term member))
theorem bit_supports (bits : Nat → Bool) :
    ∀ program ∈ programs bits, ∀ term ∈ program.low ++ program.high, term.1 ∈ kept := by
  intro program member
  simp only {unfold_members} at member
  rcases member with {branches}
'''
    source+=''.join(f'  · exact bits{offset} bits\n' for offset in range(count))
    source+=f'''theorem constructors {{F : Type}} [Field F] [CharP F modulus]
    (imaginary : F) (nonSquare : Group.NoUnitSquare (coefficientD : F))
    (imaginarySquare : imaginary*imaginary = -1) (bits : Nat → Bool) :
    ∀ program ∈ programs bits, GroupVariableCircuitCompletion.LocalConstruct
      (coefficientD : F) {copy} tables program := by
  intro program member
  simp only {unfold_members} at member
  rcases member with {branches}
'''
    source+=''.join(f'  · exact {program}.local_constructor imaginary nonSquare imaginarySquare _ _\n' for program in programs)
    source+='''private theorem local_row_member (list : List Program) (program : Program) (member : program ∈ list)
    (row : Row) (present : row ∈ program.rows) : row ∈ rows list := by
  induction list with
  | nil => exact False.elim (by simpa only [List.not_mem_nil] using member)
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | remaining
    · exact List.mem_append_left _ present
    · exact List.mem_append_right _ (ih remaining)
theorem original_rows_covered (bits : Nat → Bool) :
    ∀ row ∈ originalRows, row ∈ priorRows ++ rows (programs bits) := by
  intro row member
  obtain ⟨block,blockMember,present⟩ := List.mem_flatten.mp member
  simp only [originalBlocks,List.mem_cons,List.not_mem_nil,or_false] at blockMember
  rcases blockMember with '''+branches+'\n'
    for offset,(program,value) in enumerate(zip(programs,values)):
        membership='List.mem_cons.mpr (Or.inl rfl)'
        for _ in range(offset):membership=f'List.mem_cons.mpr (Or.inr ({membership}))'
        low_bit=2*(125-start-offset)
        source+=f'  · have covered := {program}.original_rows_covered (bits {low_bit}) (bits {low_bit+1}) row present\n'
        if start+offset==0:
            source+='''    rcases List.mem_append.mp covered with previous | current
    · exact List.mem_append_left _ previous
    · apply List.mem_append_right
      exact local_row_member _ _ (by exact '''+membership+''') row current
'''
        else:
            source+='''    apply List.mem_append_right
    exact local_row_member _ _ (by exact '''+membership+''') row covered
'''
    for export in ('certified','aligned','protected_programs','table_supports','bit_supports','constructors','original_rows_covered'):
        source+='#print axioms '+export+'\n'
    source+=f'end ShielddSecurity.{name}\n'
    return name,_signature_audits(source)
