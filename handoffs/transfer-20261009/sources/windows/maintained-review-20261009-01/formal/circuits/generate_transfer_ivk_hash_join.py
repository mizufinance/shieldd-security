"""Construct hash rows first, then preserve them through actual IVK reduction.

Only the already replayed IVK/reduction selections are used. Numeric write
fences and seed exclusions are checked independently from all field values.
This does not supply native NK/key/codec meaning or consumer nonzero.
"""
from . import generate_transfer_prefix_hash_completion as hashes
from . import transfer_ivk_reduction_completion as reduction
from . import generate_transfer_ivk_reduction_join as comparison
from .generate_hash_round import _signature_audits

H='RuntimeTransferIvkHashOwnedCompletion'
O='RuntimeTransferIvkReductionProductOrder'


def generate(ivk_data,ivk_export,reduction_data,reduction_export,parameter_root,expected_relation,readonly_lcs=()):
    selected,metadata,protected=hashes.select_ivk(ivk_data,ivk_export,parameter_root,expected_relation,readonly_lcs)
    accepted=hashes.ivk.inspect_metadata(ivk_data,parameter_root,expected_relation)
    plan=reduction.plan(reduction_data,accepted,reduction_export,expected_relation,readonly_lcs)
    q,r=plan['phases'][:2];qcol,rcol=q['value'][0][0],r['value'][0][0];qs,rs=q['start'],r['start']
    chunks,_=comparison._chunks(plan);floor=chunks[0][0]['output'];copy=metadata['constant_copy']
    context=(selected,dict(metadata=metadata),None)
    hashplans=[hashes.blocks._chunk_plan(context,i,min(i+5,65),readonly_lcs=protected) for i in range(0,65,5)]
    for chunk in hashplans:
        for row in chunk['raw'].values():
            for terms in row:
                if any(c in (qcol,rcol) or qs<=c<qs+4 or rs<=c<rs+252 or (c!=copy and c>=floor) for c,_ in terms):
                    raise reduction.relation.RelationError('IVK earlier hash exact reduction seed/product frame')
    expression=accepted['derived'][accepted['handles'][3]]
    reduction_hash=plan['checked']['expressions'][reduction.source_index(plan['checked']['metadata']['value'])]
    if expression!=reduction_hash:
        raise reduction.relation.RelationError('IVK constructed hash/reduction exact LC alias')
    width=selected['calls'][0]['parameters']['width']
    name='RuntimeTransferIvkHashReductionJoin'
    source=f'''import ShielddSecurity.{H}
import ShielddSecurity.{O}
import ShielddSecurity.RuntimeIvkHash_Composition
import ShielddSecurity.RuntimeTransferIvkReductionEndpoints
import ShielddSecurity.RuntimeTransferIvkReductionTailCompletion
import ShielddSecurity.ScalarReductionFrame
import ShielddSecurity.ColumnFence
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
namespace H := {H}
namespace O := {O}
namespace E := RuntimeTransferIvkReductionEndpoints
namespace T := RuntimeTransferIvkReductionTailCompletion
namespace D := RuntimeHashBlock_authorization_ivk_0
def completed {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) : Nat → F :=
  O.construct codec (H.completeAssignment base)
private theorem write_prefix000 : ColumnFence.checkWrites {copy} {floor} (PoseidonCompletion.writes O.prefix000) = true := rfl
'''
    for i in range(34):
        source+=f'''private theorem write_chunk{i:03d} : ColumnFence.checkWrites {copy} {floor} (PoseidonCompletion.writes O.chunk{i:03d}) = true := by decide
private theorem write_prefix{i+1:03d} : ColumnFence.checkWrites {copy} {floor} (PoseidonCompletion.writes O.prefix{i+1:03d}) = true := by
  simpa only [O.prefix{i+1:03d},ColumnFence.checkWrites,PoseidonCompletion.writes,List.flatMap_append,
    List.all_append,Bool.and_eq_true] using And.intro write_prefix{i:03d} write_chunk{i:03d}
'''
    source+=f'''theorem product_fence : ColumnFence.checkWrites {copy} {floor} (PoseidonCompletion.writes O.allStages) = true := write_prefix034
private theorem hash_link {{F : Type}} [Field F] (base : Nat → F) (linked : base {copy} = base 0) :
    H.completeAssignment base {copy} = H.completeAssignment base 0 := by
  rw [H.preserves base {copy} (by decide),H.preserves base 0 (by decide),linked]
private theorem hash_one {{F : Type}} [Field F] (base : Nat → F) (one : base 0 = 1) :
    H.completeAssignment base 0 = 1 := (H.preserves base 0 (by decide)).trans one
'''
    for i in range(13):
        chunk=f'RuntimeTransferIvkHashOwnedCompletionChunk{i}'
        source+=f'''private theorem support{i} : ∀ row ∈ {chunk}.rawRows, ∀ term ∈ row.a ++ row.b,
    term.1 ∉ [{qcol},{rcol}] ∧ (term.1 < {qs} ∨ {qs+4} ≤ term.1) ∧
    (term.1 < {rs} ∨ {rs+252} ≤ term.1) ∧ (term.1 = {copy} ∨ term.1 < {floor}) := by
  have checked : {chunk}.rawRows.all (fun row => (row.a ++ row.b).all (fun term => decide (
    term.1 ∉ [{qcol},{rcol}] ∧ (term.1 < {qs} ∨ {qs+4} ≤ term.1) ∧
    (term.1 < {rs} ∨ {rs+252} ≤ term.1) ∧ (term.1 = {copy} ∨ term.1 < {floor})))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
private theorem chunk_preserved{i} {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F)
    (constructed : Satisfies (H.completeAssignment base) {chunk}.rawRows) :
    Satisfies (completed codec base) {chunk}.rawRows := by
  apply ScalarReductionFrame.rows (H.completeAssignment base) codec (eval (H.completeAssignment base) O.hashValue)
    {qcol} {rcol} {qs} {rs} O.allStages {chunk}.rawRows constructed
  intro row member term present
  obtain ⟨seedOutside,qOutside,rOutside,productBelow⟩ := support{i} row member term present
  exact ⟨seedOutside,qOutside,rOutside,ColumnFence.checked_column {copy} {floor}
    (PoseidonCompletion.writes O.allStages) term.1 product_fence productBelow⟩
'''
    source+='''theorem hash_rows_complete {F : Type} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F)
'''
    source+=f'''    (linked : base {copy} = base 0) : Satisfies (completed codec base) H.rawRows := by
  have constructed := H.complete_rows base linked
  intro row member
  simp only [H.rawRows,RuntimeTransferIvkHashOwnedCompletionChunk12.priorRows,List.mem_append,or_assoc] at member
'''
    pattern=' | '.join(f'chunk{i}' for i in range(13))
    source+=f'  rcases member with {pattern}\n'
    for i in range(13):
        present='chunk'+str(i)
        if i:present='List.mem_append_right _ ('+present+')'
        for _ in range(12-i):present='List.mem_append_left _ ('+present+')'
        source+=f'''  · exact chunk_preserved{i} codec base (by
      intro previous previousMember
      apply constructed
      exact {present.replace('chunk'+str(i),'previousMember')}) row chunk{i}
'''
    source+=f'''theorem reduction_rows_complete {{F : Type}} [Field F]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    Satisfies (completed codec base) O.rows := O.constructs codec (H.completeAssignment base)
theorem tail_rows_complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (linked : base {copy} = base 0) : Satisfies (completed codec base) T.rawRows :=
  T.original_complete codec (H.completeAssignment base) (hash_one base one) four (hash_link base linked)
theorem complete_local_rows {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (linked : base {copy} = base 0) :
    Satisfies (completed codec base) (H.rawRows ++ O.rows ++ T.rawRows) := by
  intro row member
  rcases List.mem_append.mp member with prior | tail
  · rcases List.mem_append.mp prior with hash | reduction
    · exact hash_rows_complete codec base linked row hash
    · exact reduction_rows_complete codec base row reduction
  · exact tail_rows_complete codec base one four linked row tail
private theorem input_frame : D.callInputs.all (fun terms => terms.all (fun term => decide (
    term.1 ∉ H.ownedWrites ∧ term.1 ∉ [{qcol},{rcol}] ∧ (term.1 < {qs} ∨ {qs+4} ≤ term.1) ∧
    (term.1 < {rs} ∨ {rs+252} ≤ term.1) ∧ (term.1 = {copy} ∨ term.1 < {floor})))) = true := by decide
theorem inputs_preserved {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    D.callInputs.map (eval (completed codec base)) = D.callInputs.map (eval base) := by
  apply List.map_congr_left
  intro terms member
  apply eval_agrees
  intro term present
  obtain ⟨hashOutside,seedOutside,qOutside,rOutside,below⟩ := of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp input_frame terms member) term present)
  exact (ScalarReductionFrame.column (H.completeAssignment base) codec (eval (H.completeAssignment base) O.hashValue)
    {qcol} {rcol} {qs} {rs} O.allStages term.1 seedOutside qOutside rOutside
    (ColumnFence.checked_column {copy} {floor} (PoseidonCompletion.writes O.allStages) term.1 product_fence below)).trans
      (H.preserves base term.1 hashOutside)
theorem hash_value {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (one : base 0 = 1)
    (linked : base {copy} = base 0) :
    eval (completed codec base) O.hashValue = Poseidon.hash{width} (Poseidon.castParameters D.parameters)
      16 (D.callInputs.map (eval base)) := by
  have actualRows : Satisfies (completed codec base) D.rawRows := by
    intro row member
    exact hash_rows_complete codec base linked row
      (of_decide_eq_true (List.all_eq_true.mp H.sound_coverage_checked row member))
  have constructedOne := E.constant_one codec (H.completeAssignment base) (hash_one base one)
  have result := D.actual_hash_sound (completed codec base) constructedOne actualRows
  rw [inputs_preserved codec base] at result
  have same : Compiler.canonical Scalar.modulus O.hashValue = Compiler.canonical Scalar.modulus D.output := by decide
  exact (Compiler.canonical_equal (completed codec base) O.hashValue D.output same).trans result
'''
    for export in ('product_fence','hash_rows_complete','reduction_rows_complete','tail_rows_complete','complete_local_rows',
                   'inputs_preserved','hash_value'):
        source+='#print axioms '+export+'\n'
    return name,comparison._qualify(source+f'end ShielddSecurity.{name}\n',{'H':H,'O':O,
        'E':'RuntimeTransferIvkReductionEndpoints','T':'RuntimeTransferIvkReductionTailCompletion',
        'D':'RuntimeHashBlock_authorization_ivk_0'})
