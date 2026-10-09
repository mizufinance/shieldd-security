"""Symbolic129-bit/original-row completion for the checked actual balance slice."""
from . import transfer_signed_balance_completion as plan_source,transfer_relation as relation
from .generate_hash_round import linear,_signature_audits


def generate(metadata_bytes,stream,expected_relation):
    return _from_checked(plan_source.plan(metadata_bytes,stream,expected_relation))


def _from_checked(recipe):
    n,m=recipe['negative'],recipe['magnitude'];bits=recipe['bits'];p,a=recipe['product'],recipe['auxiliary'];copy=recipe['copy']
    if bits!=list(range(bits[0],bits[0]+129)):
        raise relation.RelationError('signed proof requires captured ascending contiguous129 bits')
    operands=[plan_source.balance.canonical(recipe[key]) for key in ('product_left','product_right')]
    neg=((n,1),);mag=((m,1),);minus2=((m,plan_source.P-2),)
    if operands not in ([neg,mag],[mag,neg],[neg,minus2],[minus2,neg]):
        raise relation.RelationError('signed proof requires exact native neg times magnitude or minus2 magnitude')
    scaled=minus2 in operands;factor=1 if scaled else -2
    want=plan_source.balance.canonical([(m,1),(p,factor)])
    if plan_source.balance.canonical(recipe['selected_expression'])!=want:
        raise relation.RelationError('signed proof selected source LC does not normalize to native signed magnitude')
    rows={row['row']:row for row in recipe['raw_rows']};roles=recipe['roles']
    def row(value):return '⟨'+linear([(c,int(v,16)) for c,v in value['a']])+','+linear([(c,int(v,16)) for c,v in value['b']])+'⟩'
    booleanRows=[row(rows[roles['range4.boolean'+str(i)]]) for i in range(129)]
    recon=row(rows[roles['range4.reconstruction']])
    productIndices=[i for i in recipe['original_row_indices'] if i not in set(roles.values())]
    if len(productIndices)!=2:raise relation.RelationError('signed proof exact original two material rows')
    boundary=[row(rows[roles[key]]) for key in ('negative.boolean','signed.equation','constant-copy')]
    canonical=plan_source.balance.canonical
    expectedBoundary=[(neg,neg),(plan_source.balance.combine(recipe['difference_expression'],recipe['selected_expression'],-1),()),((),())]
    for key in ('negative.boolean','signed.equation','constant-copy'):
        actual=rows[roles[key]]
        unoutline=lambda terms:canonical((0 if c==copy else c,int(v,16)) for c,v in terms)
        left,right=unoutline(actual['a']),unoutline(actual['b'])
        if not any(right==canonical(b) and left in (canonical(a),canonical((c,-v) for c,v in a)) for a,b in expectedBoundary):
            raise relation.RelationError('signed proof original boundary row has no exact unoutlined correspondence: '+key)
    name='RuntimeTransferSignedBalanceCompletion';start=bits[0];amounts=recipe['amounts']
    lhs,rhs=recipe['product_left'],recipe['product_right']
    expectedLeft=[(n,1)] if operands[0]==neg else [(m,-2 if scaled else 1)]
    expectedRight=[(n,1)] if operands[1]==neg else [(m,-2 if scaled else 1)]
    source=f'''import ShielddSecurity.TransferSignedMagnitude
import ShielddSecurity.ScalarCompletion
import ShielddSecurity.ScalarBitFootprint
import ShielddSecurity.CompilerSignedCompletion
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
-- Exact parent metadata SHA256 {recipe['metadata_sha256']}.
-- Actual135 local rows only; no preservation of other rows that read owned writes.
abbrev modulus := Scalar.modulus
def amountColumns (i : Fin 4) : Nat := match i.val with
  | 0 => {amounts[0]}
  | 1 => {amounts[1]}
  | 2 => {amounts[2]}
  | _ => {amounts[3]}
def roots : List Nat := [{n},{m}]
def bitColumns : List Nat := List.range' {start} 129
def writes : List Nat := roots ++ bitColumns ++ [{p},{a}]
def rawBooleanRows : List Row := [
'''+',\n'.join(booleanRows)+f''']
def rawReconstruction : Row := {recon}
def rawRangeRows : List Row := rawBooleanRows ++ [rawReconstruction]
def rangeRows : List Row := bitColumns.map booleanRow ++ [reconstructionRow {m} bitColumns]
def rawProductRows : List Row := [{','.join(row(rows[i]) for i in productIndices)}]
def productRows : List Row := ScalarCompletion.productRows {linear(lhs)} {linear(rhs)} [] {p} {a}
def rawBoundaryRows : List Row := [{','.join(boundary)}]
def difference : Linear := {linear(recipe['difference_expression'])}
def selected : Linear := {linear(recipe['selected_expression'])}
-- The original constant-copy equality becomes the empty row after unoutlining.
-- Its actual satisfaction still requires the preserved copy=one link below.
def boundaryRows : List Row := [booleanRow {n},⟨Compiler.subtract difference selected,[]⟩,⟨[],[]⟩]
def rawRows : List Row := rawRangeRows ++ rawProductRows ++ rawBoundaryRows
variable {{F : Type}} [Field F] [CharP F modulus] [DecidableEq F]
def rootValues (amounts : TransferSignedMagnitude.Inputs) (column : Nat) : F :=
  if column = {n} then if TransferSignedMagnitude.negative amounts then 1 else 0
  else (TransferSignedMagnitude.magnitude amounts : F)
def rootAssignment (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs) : Nat → F :=
  patchAssignment rho (rootValues amounts) roots
def bitAssignment (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs) : Nat → F :=
  writeBits (rootAssignment rho amounts) {start} (encodeBits 129 (TransferSignedMagnitude.magnitude amounts))
def completeAssignment (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs) : Nat → F :=
  ScalarCompletion.extendProduct (bitAssignment rho amounts) {linear(lhs)} {linear(rhs)} [] {p} {a}

theorem preserves (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs)
    (column : Nat) (outside : column ∉ writes) : completeAssignment rho amounts column = rho column := by
  have rootsOutside : column ∉ roots := by
    intro member; apply outside; simp only [writes,List.mem_append]; exact Or.inl (Or.inl member)
  have bitsOutside : column ∉ bitColumns := by
    intro member; apply outside; simp only [writes,List.mem_append]; exact Or.inl (Or.inr member)
  have productOutside : column ∉ [{p},{a}] := by
    intro member; apply outside; simp only [writes,List.mem_append]; exact Or.inr member
  have interval : column < {start} ∨ {start}+129 ≤ column := by
    simp only [bitColumns,List.mem_range'_1] at bitsOutside
    omega
  unfold completeAssignment bitAssignment
  rw [ScalarCompletion.extend_product_preserves _ _ _ _ _ _ _ productOutside,
    writeBits_preserves _ _ _ column (by simpa using interval)]
  exact patchAssignment_preserves rho _ roots column rootsOutside

theorem bit_negative (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs) :
    bitAssignment rho amounts {n} = if TransferSignedMagnitude.negative amounts then 1 else 0 := by
  unfold bitAssignment
  rw [writeBits_preserves _ _ _ {n} (by simp only [encodeBits_length]; omega)]
  simp [rootAssignment,patchAssignment,roots,rootValues]
theorem bit_magnitude (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs) :
    bitAssignment rho amounts {m} = (TransferSignedMagnitude.magnitude amounts : F) := by
  unfold bitAssignment
  rw [writeBits_preserves _ _ _ {m} (by simp only [encodeBits_length]; omega)]
  simp [rootAssignment,patchAssignment,roots,rootValues]
theorem final_negative (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs) :
    completeAssignment rho amounts {n} = if TransferSignedMagnitude.negative amounts then 1 else 0 := by
  unfold completeAssignment
  rw [ScalarCompletion.extend_product_preserves _ _ _ _ _ _ _ (by decide)]
  exact bit_negative rho amounts
theorem final_magnitude (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs) :
    completeAssignment rho amounts {m} = (TransferSignedMagnitude.magnitude amounts : F) := by
  unfold completeAssignment
  rw [ScalarCompletion.extend_product_preserves _ _ _ _ _ _ _ (by decide)]
  exact bit_magnitude rho amounts

theorem range_complete (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs) :
    Satisfies (completeAssignment rho amounts) rangeRows := by
  have initial : Satisfies (bitAssignment rho amounts) rangeRows := by
    apply writeBits_range_complete (rootAssignment rho amounts) {m} {start} 129
      (TransferSignedMagnitude.magnitude amounts) (TransferSignedMagnitude.magnitude_bound amounts)
    · simp [rootAssignment,patchAssignment,roots,rootValues]
    · omega
  have below : ScalarRandomizerBounds.RowsBelow {p} rangeRows :=
    ScalarBitFootprint.initial_rows_below {m} {start} 129 {p} (by decide) (by decide)
  apply ScalarCompletion.extend_product_preserves_rows _ _ _ _ _ _ rangeRows initial
  intro current present term member written
  have small := below current present term member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at written
  rcases written with same | same <;> omega

theorem product_complete (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs) :
    Satisfies (completeAssignment rho amounts) productRows := by
  apply ScalarCompletion.extend_product_complete _ _ _ _ _ _ (by decide)
  intro term member
  simp only [List.append_nil,List.mem_append,List.mem_singleton] at member
  rcases member with rfl | rfl <;> decide

theorem product_value (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs) :
    completeAssignment rho amounts {p} =
      (if TransferSignedMagnitude.negative amounts then (1 : F) else 0) *
      {'(-2 : F) * ' if scaled else ''}(TransferSignedMagnitude.magnitude amounts : F) := by
  have leftValue := Compiler.canonical_equal (bitAssignment rho amounts) {linear(lhs)} {linear(expectedLeft)} (by decide)
  have rightValue := Compiler.canonical_equal (bitAssignment rho amounts) {linear(rhs)} {linear(expectedRight)} (by decide)
  have empty : eval (bitAssignment rho amounts) [] = (0 : F) := rfl
  simp only [completeAssignment,ScalarCompletion.extendProduct,patchAssignment,
    List.mem_cons_self,if_true,if_pos rfl,ScalarCompletion.productValues,empty,sub_zero]
  rw [leftValue,rightValue]
  simp only [eval,Int.cast_neg,Int.cast_one,Int.cast_ofNat,Nat.cast_ofNat,
    one_mul,add_zero,bit_negative,bit_magnitude]
  ring

theorem selected_value (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs) :
    eval (completeAssignment rho amounts) selected = (TransferSignedMagnitude.magnitude amounts : F) -
      2 * (if TransferSignedMagnitude.negative amounts then (1 : F) else 0) * (TransferSignedMagnitude.magnitude amounts : F) := by
  have normalized := Compiler.canonical_equal (completeAssignment rho amounts) selected
    ([( {m},1)] ++ scaleLinear ({factor}) [({p},1)]) (by decide)
  rw [normalized,eval_append,eval_scale]
  simp only [eval,Int.cast_one,Int.cast_neg,Int.cast_ofNat,Nat.cast_ofNat,one_mul,add_zero,
    final_magnitude,product_value]
  ring

theorem boundary_complete (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0)
    (nativeAmounts : ∀ i, rho (amountColumns i) = ((amounts i).val : F)) :
    Satisfies (completeAssignment rho amounts) boundaryRows := by
  have finalOne : completeAssignment rho amounts 0 = 1 := by rw [preserves _ _ 0 (by decide),one]
  have amountsOutside : ∀ i : Fin 4, amountColumns i ∉ writes := by decide
  have inputs : ∀ i, completeAssignment rho amounts (amountColumns i) = ((amounts i).val : F) := by
    intro i
    rw [preserves _ _ _ (amountsOutside i)]
    exact nativeAmounts i
  have differenceValue := Compiler.canonical_equal (completeAssignment rho amounts) difference
    {linear([(amounts[0],1),(amounts[1],1),(amounts[2],-1),(amounts[3],-1)])} (by decide)
  have nativeDifference : eval (completeAssignment rho amounts) difference =
      ((amounts 0).val : F) + ((amounts 1).val : F) - ((amounts 2).val : F) - ((amounts 3).val : F) := by
    rw [differenceValue]
    have h0 := inputs 0; have h1 := inputs 1; have h2 := inputs 2; have h3 := inputs 3
    change completeAssignment rho amounts {amounts[0]} = ((amounts 0).val : F) at h0
    change completeAssignment rho amounts {amounts[1]} = ((amounts 1).val : F) at h1
    change completeAssignment rho amounts {amounts[2]} = ((amounts 2).val : F) at h2
    change completeAssignment rho amounts {amounts[3]} = ((amounts 3).val : F) at h3
    simp only [eval,Int.cast_neg,Int.cast_one,neg_one_mul,one_mul,add_zero,h0,h1,h2,h3]
    ring
  intro current member
  simp only [boundaryRows,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · simpa only [booleanRow,eval,Int.cast_one,one_mul,add_zero,final_negative] using
      (TransferSignedMagnitude.negative_boolean (F := F) amounts)
  · change Square (eval (completeAssignment rho amounts) (Compiler.subtract difference selected)) 0
    rw [Compiler.eval_subtract,nativeDifference,selected_value,TransferSignedMagnitude.field_equation,sub_self]
    exact zero_mul 0
  · exact zero_mul 0

theorem boolean_identity : rawBooleanRows = bitColumns.map booleanRow := by decide
theorem reconstruction_checked :
    (Compiler.canonical modulus (Compiler.unoutline {copy} rawReconstruction.a) =
        Compiler.canonical modulus (reconstructionRow {m} bitColumns).a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} rawReconstruction.a) =
        Compiler.canonical modulus (scaleLinear (-1) (reconstructionRow {m} bitColumns).a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} rawReconstruction.b) =
      Compiler.canonical modulus (reconstructionRow {m} bitColumns).b := by decide
theorem product_coverage_checked : rawProductRows.all (fun actual => productRows.any (fun expected => decide (
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide
theorem boundary_coverage_checked : rawBoundaryRows.all (fun actual => boundaryRows.any (fun expected => decide (
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
     Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide

theorem original_rows_complete (rho : Nat → F) (amounts : TransferSignedMagnitude.Inputs)
    (one : rho 0 = 1) (linked : rho {copy} = rho 0)
    (nativeAmounts : ∀ i, rho (amountColumns i) = ((amounts i).val : F)) :
    Satisfies (completeAssignment rho amounts) rawRows := by
  have finalLink : completeAssignment rho amounts {copy} = completeAssignment rho amounts 0 := by
    rw [preserves _ _ {copy} (by decide),preserves _ _ 0 (by decide),linked]
  have range := range_complete rho amounts
  have originalRange : Satisfies (completeAssignment rho amounts) rawRangeRows := by
    intro current member
    simp only [rawRangeRows,List.mem_append,List.mem_singleton] at member
    rcases member with boolean | rfl
    · rw [boolean_identity] at boolean
      exact range current (List.mem_append_left _ boolean)
    · have expected := range (reconstructionRow {m} bitColumns) (List.mem_append_right _ (List.mem_singleton_self _))
      have transported := CompilerSignedCompletion.signed_row (completeAssignment rho amounts)
        (⟨Compiler.unoutline {copy} rawReconstruction.a,Compiler.unoutline {copy} rawReconstruction.b⟩ : Row)
        (reconstructionRow {m} bitColumns) reconstruction_checked.1 reconstruction_checked.2 expected
      simpa only [Compiler.eval_unoutline _ {copy} _ finalLink] using transported
  have originalProduct : Satisfies (completeAssignment rho amounts) rawProductRows := by
    apply CompilerSignedCompletion.original_rows _ productRows rawProductRows {copy} finalLink (product_complete rho amounts)
    intro actual member
    obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp (List.all_eq_true.mp product_coverage_checked actual member)
    exact ⟨expected,present,of_decide_eq_true equations⟩
  have originalBoundary : Satisfies (completeAssignment rho amounts) rawBoundaryRows := by
    apply CompilerSignedCompletion.original_rows _ boundaryRows rawBoundaryRows {copy} finalLink (boundary_complete rho amounts one linked nativeAmounts)
    intro actual member
    obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp (List.all_eq_true.mp boundary_coverage_checked actual member)
    exact ⟨expected,present,of_decide_eq_true equations⟩
  intro current member
  simp only [rawRows,List.mem_append] at member
  rcases member with (member | member) | member
  · exact originalRange current member
  · exact originalProduct current member
  · exact originalBoundary current member
'''
    exports=['preserves','bit_negative','bit_magnitude','final_negative','final_magnitude','range_complete','product_complete',
        'product_value','selected_value','boundary_complete','boolean_identity','reconstruction_checked',
        'product_coverage_checked','boundary_coverage_checked','original_rows_complete']
    source+=''.join('#print axioms '+export+'\n' for export in exports)
    return name,_signature_audits(source+'end ShielddSecurity.'+name+'\n')
