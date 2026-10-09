"""Reverse certificates for the genuine captured signed-balance relation."""
from . import generate_transfer_signed_balance_completion as completion
from . import transfer_signed_balance_completion as ingress
from .generate_hash_round import linear, _signature_audits


def generate(metadata_bytes, stream, expected_relation):
    return render_checked(ingress.plan(metadata_bytes, stream, expected_relation))


def render_checked(recipe):
    # Reuse the source/operand/row validation, without changing the existing
    # completion generator or duplicating its construction proofs.
    completion._from_checked(recipe)
    negative, magnitude = recipe['negative'], recipe['magnitude']
    product, auxiliary, copy = recipe['product'], recipe['auxiliary'], recipe['copy']
    left, right = linear(recipe['product_left']), linear(recipe['product_right'])
    canonical = ingress.balance.canonical
    operands = [canonical(recipe[key]) for key in ('product_left', 'product_right')]
    scaled = ((magnitude, ingress.P - 2),) in operands
    factor = 1 if scaled else -2
    compact = [linear([(negative, 1)]) if operand == ((negative, 1),)
               else linear([(magnitude, -2 if scaled else 1)]) for operand in operands]
    name = 'RuntimeTransferSignedBalanceSoundness'
    source = f'''import ShielddSecurity.RuntimeTransferSignedBalanceCompletion
import ShielddSecurity.ScalarBooleanReflection
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
namespace ShielddSecurity.{name}
abbrev modulus := Scalar.modulus
def expectedRows : List Row := [reconstructionRow {magnitude} C.bitColumns] ++
  C.productRows ++ C.boundaryRows

/-- Only the six non-bit rows require finite reverse searches. Bit rows use
the already captured symbolic map identity, avoiding quadratic bit searches. -/
theorem reverse_checked : expectedRows.all (fun row =>
    Compiler.checkRow modulus (Compiler.unoutlineRows {copy} C.rawRows) row ||
    Compiler.checkRow modulus (Compiler.unoutlineRows {copy} C.rawRows)
      ⟨scaleLinear (-1) row.a,row.b⟩) = true := by decide

theorem expected_from_actual {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho C.rawRows) :
    Satisfies rho expectedRows := by
  have normalized := Compiler.unoutline_rows_sound rho {copy} C.rawRows satisfied (by decide)
  intro row member
  have checked := List.all_eq_true.mp reverse_checked row member
  simp only [Bool.or_eq_true] at checked
  rcases checked with direct | reversed
  · exact Compiler.checked_row_sound rho _ row normalized direct
  · have truth := Compiler.checked_row_sound rho _
      ⟨scaleLinear (-1) row.a,row.b⟩ normalized reversed
    simpa only [eval_scale,Int.cast_neg,Int.cast_one,neg_one_mul,
      Square,neg_mul_neg] using truth

theorem magnitude_from_actual {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (satisfied : Satisfies rho C.rawRows) :
    ∃ n : Nat, n < 2^129 ∧ (n : F) = rho {magnitude} := by
  have booleans : Satisfies rho (C.bitColumns.map booleanRow) := by
    rw [← C.boolean_identity]
    intro row member
    exact satisfied row (by
      simp only [C.rawRows,C.rawRangeRows,List.mem_append,List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl member)))
  have expected := expected_from_actual rho satisfied
  have reconstructed := expected (reconstructionRow {magnitude} C.bitColumns)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton_self _)))
  obtain ⟨n,bound,value⟩ := ScalarBooleanReflection.columns_value rho C.bitColumns
    {magnitude} booleans reconstructed
  exact ⟨n,by simpa only [C.bitColumns,List.length_range'] using bound,value⟩

/-- The sign and selected field difference are row consequences on this same
assignment. Four nonzero is the explicit standard product-encoding premise. -/
theorem signed_from_actual {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho C.rawRows) :
    ∃ sign : Bool, rho {negative} = (if sign then 1 else 0) ∧
      eval rho C.difference =
        rho {magnitude} - 2 * (if sign then 1 else 0) * rho {magnitude} := by
  classical
  have expected := expected_from_actual rho satisfied
  have boundary : Satisfies rho C.boundaryRows := by
    intro row member
    exact expected row (List.mem_append_right _ member)
  have signRow := boundary (booleanRow {negative}) (by simp [C.boundaryRows])
  have signValue := ScalarBits.decoded_bit_value rho [({negative},1)]
    (by simpa only [booleanRow] using signRow)
  have product := Compiler.checked_product_sound rho expectedRows {left} {right}
    [({product},1)] [({auxiliary},1)] four expected (by decide) (by decide)
  have leftValue := Compiler.canonical_equal (p := modulus) rho {left} {compact[0]} (by decide)
  have rightValue := Compiler.canonical_equal (p := modulus) rho {right} {compact[1]} (by decide)
  rw [leftValue,rightValue] at product
  have selected := Compiler.checked_assertion_sound rho expectedRows C.difference C.selected
    expected (by decide)
  have selection := Compiler.canonical_equal (p := modulus) rho C.selected
    [({magnitude},1),({product},{factor})] (by decide)
  refine ⟨ScalarBits.decodeBit rho [({negative},1)],?_,?_⟩
  · simpa only [eval,Int.cast_one,one_mul,add_zero] using signValue
  · simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_neg,Int.cast_ofNat] at product signValue
    rw [selected,selection]
    simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat,Int.cast_neg]
    rw [product,signValue]
    ring

theorem actual_rows_sound {{F : Type}} [Field F] [CharP F modulus]
    (rho : Nat → F) (four : (4 : F) ≠ 0) (satisfied : Satisfies rho C.rawRows) :
    ∃ n : Nat, ∃ sign : Bool, n < 2^129 ∧ (n : F) = rho {magnitude} ∧
      rho {negative} = (if sign then 1 else 0) ∧
      eval rho C.difference = if sign then -(n : F) else (n : F) := by
  obtain ⟨n,bound,value⟩ := magnitude_from_actual rho satisfied
  obtain ⟨sign,signValue,difference⟩ := signed_from_actual rho four satisfied
  refine ⟨n,sign,bound,value,signValue,?_⟩
  rw [difference,← value]
  cases sign <;> simp only [Bool.false_eq_true,if_false,if_true] <;> ring

#print axioms reverse_checked
#print axioms expected_from_actual
#print axioms magnitude_from_actual
#print axioms signed_from_actual
#print axioms actual_rows_sound
end ShielddSecurity.{name}
'''
    source = source.replace('C.', 'RuntimeTransferSignedBalanceCompletion.')
    return name, _signature_audits(source)
