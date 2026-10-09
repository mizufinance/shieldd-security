"""Genuine H canonical and fixed126 composition.

Own H ingress checks the committed blinding scalar's actual private column and
physical canonical bit allocation. Scalar zero remains a legal input.
"""
from . import transfer_balance_blinding_program as whole
from . import transfer_fixed_spend as fixed, transfer_relation as relation
from .generate_hash_round import _signature_audits, signed


def generate(parent,pages,expected_base,expected_blinding,extracted,*,readonly_lcs=()):
    accepted=whole.plan(parent,pages,expected_base,expected_blinding,extracted,readonly_lcs)
    if (len(accepted['loop']['programs'])!=126 or len(accepted['checked']['chunks'])!=8 or
            accepted['canonical']['bit_start']!=22232 or accepted['canonical']['value']!=9 or
            accepted['bounds']['constant_copy']!=200692):
        raise relation.RelationError('VALUE_BLINDING exact original private/bit/copy source allocation')
    bounds = accepted['bounds']
    if (bounds['constant_copy'] != 200692 or len(bounds['frames']) != 126 or
            bounds['frames'][0]['before'] != {'low': 22484, 'high': 193210} or
            bounds['frames'][0]['after'] != {'low': 22486, 'high': 193214}):
        raise relation.RelationError('canonical preservation actual folded allocation frame')
    high_start, copy = bounds['high_start'], bounds['constant_copy']
    c = 'RuntimeBalanceBlindingCanonical'
    r = 'RuntimeBalanceBlindingCanonicalCompletion'
    p = 'RuntimeBalanceBlindingWindow000TemplatePrefix'
    first = 'RuntimeBalanceBlindingWindow000'
    t = 'RuntimeBalanceBlindingTemplateOrdinaryTrace'
    prior = 'RuntimeBalanceBlindingTemplateOrdinaryPrior'
    ingress = 'RuntimeBalanceBlindingTemplateCanonicalIngress'
    before = 'RuntimeBalanceBlindingWindow001TemplateTrace.before'
    ns = 'RuntimeBalanceBlindingTemplateCanonicalPreservation'
    helper = 'GroupFixedPriorPreservation'
    low = '(encodeBits 252 n)[0]?.getD false'
    high = '(encodeBits 252 n)[1]?.getD false'
    d = signed(fixed.D)
    source = f'''import ShielddSecurity.{ingress}
import ShielddSecurity.{helper}
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

private theorem checked_part (rows : List Row)
    (checked : rows.all (fun row => (row.a ++ row.b).all (fun term =>
      decide (GroupFixedCircuitBounds.covers {high_start} {copy} {p}.before term.1))) = true) :
    GroupFixedCircuitBounds.RowsCovered {high_start} {copy} {p}.before rows := by
  intro row member term present
  exact of_decide_eq_true
    (List.all_eq_true.mp (List.all_eq_true.mp checked row member) term present)
'''
    parts = [f'c{i}Raw' for i in range(16)] + ['tailRaw']
    for i, part in enumerate(parts):
        source += f'''
private theorem part{i:02d}_covered : GroupFixedCircuitBounds.RowsCovered
    {high_start} {copy} {p}.before {c}.{part} := checked_part _ (by decide)
'''
    source += f'''
theorem canonical_rows_covered : GroupFixedCircuitBounds.RowsCovered
    {high_start} {copy} {p}.before {c}.originalRows := by
  intro row member term present
  obtain ⟨block,inside,rowMember⟩ := List.mem_flatten.mp member
  simp only [{c}.originalBlocks,List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with {' | '.join('rfl' for _ in parts)}
'''
    for i in range(len(parts)):
        source += f'  · exact part{i:02d}_covered row rowMember term present\n'
    source += f'''
theorem prefix_fresh (low high : Bool) : GroupFixedCircuitCompletion.Fresh
    {c}.originalRows [{p}.program low high] := by
  have certificate := {p}.checked_bounds low high
  have done := GroupFixedCircuitBounds.bounded_fresh {high_start} {copy} {p}.before
    {c}.originalRows [({p}.program low high,{p}.after)] canonical_rows_covered
    ⟨certificate.1,certificate.2.1,certificate.2.2,trivial⟩
  exact done

theorem ordinary_fresh (n : Nat) : GroupFixedCircuitCompletion.Fresh
    {c}.originalRows (({t}.windows n).map GroupFixedTemplateTrace.Window.program) := by
  apply {prior}.prior_fresh n
  exact {helper}.rows_covered_mono {high_start} {copy} {p}.before {before}
    {c}.originalRows (by decide) canonical_rows_covered

def construct {{F : Type}} [Field F] (rho : Nat → F) (n : Nat) : Nat → F :=
  GroupFixedCircuitCompletion.run (({p}.program ({low}) ({high})).build ({r}.construct rho n))
    (({t}.windows n).map GroupFixedTemplateTrace.Window.program)

theorem canonical_rows_preserved {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    (rho : Nat → F) (n : Nat) (canonical : n < Scalar.order)
    (meaning : rho 9 = (n : F)) (one : rho 0 = 1) (linked : rho {copy} = rho 0)
    (four : (4 : F) ≠ 0) : Satisfies (construct rho n) {c}.originalRows := by
  have initial := {r}.actual_original_rows_complete rho n canonical meaning one four linked
  have prefixDone := {helper}.run_preserves_prior ({r}.construct rho n)
    [{p}.program ({low}) ({high})] {c}.originalRows (prefix_fresh ({low}) ({high})) initial
  exact {helper}.run_preserves_prior _ _ {c}.originalRows (ordinary_fresh n) prefixDone

theorem actual_canonical_and_fixed126_complete {{F : Type}} [Field F] [CharP F {relation.MODULUS}]
    {{J : Type}} [AddCommGroup J] (model : Group.StandardCurveModel J (({d} : Int) : F))
    (rho : Nat → F) (n : Nat) (generator : J) (canonical : n < Scalar.order)
    (meaning : rho 9 = (n : F)) (one : rho 0 = 1) (linked : rho {copy} = rho 0) (four : (4 : F) ≠ 0)
    (imaginary : F) (nonSquare : Group.NoUnitSquare (({d} : Int) : F))
    (imaginarySquare : imaginary*imaginary = -1)
    (baseMeaning : ({first}.base : Group.Point F) = model.coordinates generator) :
    Satisfies (construct rho n) ({c}.originalRows ++ ({first}.rawRows ++
      GroupFixedCircuitCompletion.rows (({t}.windows n).map GroupFixedTemplateTrace.Window.program))) ∧
    GroupFixedCircuitCompletion.point (construct rho n)
      (GroupFixedTemplateTrace.endpoint {t}.input ({t}.windows n)) =
      model.coordinates (n • generator) := by
  have rows := canonical_rows_preserved rho n canonical meaning one linked four
  have done := {ingress}.actual_native_scalar_from_canonical model rho n generator canonical
    meaning one linked four imaginary nonSquare imaginarySquare baseMeaning
  refine ⟨?_,done.2.2⟩
  intro row member
  rcases List.mem_append.mp member with earlier | windows
  · exact rows row earlier
  · exact done.1 row windows

#print axioms canonical_rows_covered
#print axioms prefix_fresh
#print axioms ordinary_fresh
#print axioms canonical_rows_preserved
#print axioms actual_canonical_and_fixed126_complete
end ShielddSecurity.{ns}
'''
    return ns, _signature_audits(source)
