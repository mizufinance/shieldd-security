"""Finish the actual IVK inverse after the independently constructed prefix.

This renderer consumes already accepted typed row exports. It never scans a
relation or qualifies a candidate. The sole division legality contract concerns
the globally decoded hash of the source call inputs, not a witness column.
"""
from . import generate_transfer_ivk_reduction_join as joins
from . import transfer_ivk_reduction_completion as reduction


def generate(data, accepted_ivk, extracted, expected_relation, readonly_lcs=()):
    plan = reduction.plan(data, accepted_ivk, extracted, expected_relation, readonly_lcs)
    inverse = plan['inverse']
    q, r = plan['phases'][:2]
    qcol, rcol = q['value'][0][0], r['value'][0][0]
    qs, rs = q['start'], r['start']
    writes = [inverse[key] for key in ('quotient', 'product', 'auxiliary')]
    weighted = tuple((rs+i, 2**i) for i in range(252))
    if inverse['denominator'] != weighted or len(set(writes)) != 3:
        raise reduction.relation.RelationError('actual inverse denominator/write shape')
    prior = set(plan['raw']) - set(inverse['rows'])
    if len(prior) != 1275 or any(column in writes for index in prior
            for terms in plan['raw'][index] for column, _ in terms):
        raise reduction.relation.RelationError('actual inverse prior-row support exclusion')
    copy = plan['checked']['metadata']['constant_copy']
    parts = [f'RuntimeTransferIvkComparison{phase["phase"]}OriginalChunk{i}'
             for phase in plan['phases'] for i in range((phase['width']+15)//16)]
    parts += ['RuntimeTransferIvkGateProductOriginal', 'RuntimeTransferIvkReductionTailCompletion']
    hashparts = [f'RuntimeTransferIvkHashOwnedCompletionChunk{i}' for i in range(13)]
    name = 'RuntimeTransferIvkInversePrefixJoin'
    aliases = dict(C='RuntimeTransferIvkHashReductionJoin', O=joins.ORDER,
        H='RuntimeTransferIvkHashOwnedCompletion', I='RuntimeTransferIvkInverseOwnedCompletion',
        R='RuntimeTransferIvkReductionOriginalRows', D='RuntimeHashBlock_authorization_ivk_0')
    source = ''.join(f'import ShielddSecurity.{module}\n' for module in
        [aliases[key] for key in ('C', 'I', 'R')])
    source += '''import ShielddSecurity.ScalarWrittenValue
import ShielddSecurity.ScalarReductionSupport
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
'''
    source += f'namespace ShielddSecurity.{name}\n'
    source += ''.join(f'namespace {key} := {value}\n' for key, value in aliases.items())
    source += '''def completed {F : Type} [Field F] (codec : TransferReduction.CanonicalField F)
    (base : Nat → F) : Nat → F := I.construct (C.completed codec base)
def originalRows : List Row := H.rawRows ++ R.originalRows ++ I.rawRows
'''
    source += f'''private theorem denominator_shape : I.denominator = weighted (List.range' {rs} 252) 1 := by decide
private theorem hash_kept : ∀ term ∈ O.hashValue, term.1 ∈ O.kept ∧ term.1 ∉ [{qcol},{rcol}] ∧
    (term.1 < {qs} ∨ {qs+4} ≤ term.1) ∧ (term.1 < {rs} ∨ {rs+252} ≤ term.1) := by
  have checked : O.hashValue.all (fun term => decide (term.1 ∈ O.kept ∧ term.1 ∉ [{qcol},{rcol}] ∧
    (term.1 < {qs} ∨ {qs+4} ≤ term.1) ∧ (term.1 < {rs} ∨ {rs+252} ≤ term.1))) = true := by decide
  intro term member
  exact of_decide_eq_true (List.all_eq_true.mp checked term member)
private theorem seed_hash {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    eval (C.completed codec base) O.hashValue = eval (H.completeAssignment base) O.hashValue :=
  ScalarReductionSupport.hash_preserved (H.completeAssignment base) codec (eval (H.completeAssignment base) O.hashValue)
    {qcol} {rcol} {qs} {rs} O.allStages O.kept O.ordered O.hashValue hash_kept
theorem consumer_value {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F) :
    eval (C.completed codec base) I.denominator =
      (ScalarReductionSeed.remainder codec (eval (H.completeAssignment base) O.hashValue) : F) := by
  rw [denominator_shape]
  exact ScalarWrittenValue.remainder_value _ _ codec _ {rs}
    (ScalarReductionSupport.written_remainder_bits (H.completeAssignment base) codec
      (eval (H.completeAssignment base) O.hashValue) {qcol} {rcol} {qs} {rs} O.allStages O.kept O.ordered)
theorem denominator_nonzero {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (one : base 0 = 1)
    (linked : base {copy} = base 0)
    (legalInput : codec.decode (Poseidon.hash6 (Poseidon.castParameters D.parameters) 16
      (D.callInputs.map (eval base))) % Scalar.order ≠ 0) :
    eval (C.completed codec base) I.denominator ≠ 0 := by
  have same := (seed_hash codec base).symm.trans (C.hash_value codec base one linked)
  have legalSeed : codec.decode (eval (H.completeAssignment base) O.hashValue) % Scalar.order ≠ 0 := by
    rw [same]
    exact legalInput
  rw [denominator_shape]
  exact ScalarWrittenValue.remainder_nonzero _ _ codec _ {rs}
    (ScalarReductionSupport.written_remainder_bits (H.completeAssignment base) codec
      (eval (H.completeAssignment base) O.hashValue) {qcol} {rcol} {qs} {rs} O.allStages O.kept O.ordered) legalSeed
private theorem prefix_link {{F : Type}} [Field F] (codec : TransferReduction.CanonicalField F) (base : Nat → F)
    (linked : base {copy} = base 0) : C.completed codec base {copy} = C.completed codec base 0 := by
  have hashLink : H.completeAssignment base {copy} = H.completeAssignment base 0 := by
    rw [H.preserves base {copy} (by decide),H.preserves base 0 (by decide),linked]
  have left := ScalarReductionSupport.kept_column (H.completeAssignment base) codec
    (eval (H.completeAssignment base) O.hashValue) {qcol} {rcol} {qs} {rs} O.allStages O.kept O.ordered
    {copy} (by decide) (by decide) (by decide) (by decide)
  have right := ScalarReductionSupport.kept_column (H.completeAssignment base) codec
    (eval (H.completeAssignment base) O.hashValue) {qcol} {rcol} {qs} {rs} O.allStages O.kept O.ordered
    0 (by decide) (by decide) (by decide) (by decide)
  exact left.trans (hashLink.trans right.symm)
'''
    for index, part in enumerate(parts+hashparts):
        source += f'''private theorem support{index} : ∀ row ∈ {part}.rawRows, ∀ term ∈ row.a ++ row.b,
    term.1 ∉ I.ownedWrites := by
  have checked : {part}.rawRows.all (fun row => (row.a ++ row.b).all
    (fun term => decide (term.1 ∉ I.ownedWrites))) = true := by decide
  intro row member term present
  exact of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
'''
    # Traverse only the outer lists. The bounded support certificates above are
    # never replaced with a full1275-row reduction of an executable checker.
    source += '''private theorem reduction_support : ∀ row ∈ R.originalRows, ∀ term ∈ row.a ++ row.b,
    term.1 ∉ I.ownedWrites := by
  intro row member term present
  rcases List.mem_append.mp member with materialization | tail
  · obtain ⟨part,partMember,rowMember⟩ := List.mem_flatten.mp materialization
    simp only [R.parts,List.mem_cons,List.not_mem_nil,or_false] at partMember
'''
    source += '    rcases partMember with ' + ' | '.join('rfl' for _ in parts[:-1]) + '\n'
    for index in range(len(parts)-1):
        source += f'    · exact support{index} row rowMember term present\n'
    source += f'  · exact support{len(parts)-1} row tail term present\n'
    source += '''private theorem hash_support : ∀ row ∈ H.rawRows, ∀ term ∈ row.a ++ row.b,
    term.1 ∉ I.ownedWrites := by
  intro row member term present
  simp only [H.rawRows,RuntimeTransferIvkHashOwnedCompletionChunk12.priorRows,List.mem_append,or_assoc] at member
'''
    source += '  rcases member with ' + ' | '.join(f'chunk{i}' for i in range(13)) + '\n'
    for index in range(13):
        source += f'  · exact support{len(parts)+index} row chunk{index} term present\n'
    source += f'''theorem original_reduction_complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (linked : base {copy} = base 0) : Satisfies (completed codec base) R.originalRows := by
  have hashLink : H.completeAssignment base {copy} = H.completeAssignment base 0 := by
    rw [H.preserves base {copy} (by decide),H.preserves base 0 (by decide),linked]
  have hashOne : H.completeAssignment base 0 = 1 := (H.preserves base 0 (by decide)).trans one
  exact GroupRowCompletion.preserves_rows (C.completed codec base) I.numerator I.denominator I.remainder
    {writes[0]} {writes[1]} {writes[2]} R.originalRows
    (R.original_complete codec (H.completeAssignment base) hashOne four hashLink) reduction_support
theorem original_hash_complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (linked : base {copy} = base 0) :
    Satisfies (completed codec base) H.rawRows :=
  GroupRowCompletion.preserves_rows (C.completed codec base) I.numerator I.denominator I.remainder
    {writes[0]} {writes[1]} {writes[2]} H.rawRows (C.hash_rows_complete codec base linked) hash_support
theorem original_complete {{F : Type}} [Field F] [CharP F Scalar.modulus]
    (codec : TransferReduction.CanonicalField F) (base : Nat → F) (one : base 0 = 1) (four : (4 : F) ≠ 0)
    (linked : base {copy} = base 0)
    (legalInput : codec.decode (Poseidon.hash6 (Poseidon.castParameters D.parameters) 16
      (D.callInputs.map (eval base))) % Scalar.order ≠ 0) : Satisfies (completed codec base) originalRows := by
  have inverseRows := I.complete (C.completed codec base) (prefix_link codec base linked)
    (denominator_nonzero codec base one linked legalInput)
  intro row member
  rcases List.mem_append.mp member with prior | inverse
  · rcases List.mem_append.mp prior with hash | reduction
    · exact original_hash_complete codec base linked row hash
    · exact original_reduction_complete codec base one four linked row reduction
  · exact inverseRows row inverse
'''
    for export in ('consumer_value', 'denominator_nonzero', 'original_reduction_complete',
                   'original_hash_complete', 'original_complete'):
        source += '#print axioms ' + export + '\n'
    return name, joins._qualify(source+f'end ShielddSecurity.{name}\n', aliases)
