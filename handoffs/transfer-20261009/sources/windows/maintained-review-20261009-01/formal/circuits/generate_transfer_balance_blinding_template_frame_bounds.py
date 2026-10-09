"""Actual H write separation from small scalar chunks and symbolic window bounds."""
from . import transfer_balance_blinding_program as whole, transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(parent, pages, expected_base, expected_blinding, extracted, *, readonly_lcs=()):
    accepted = whole.plan(parent, pages, expected_base, expected_blinding, extracted, readonly_lcs)
    canonical = accepted['canonical']
    chunks = canonical['chunks']
    if (canonical['bit_start'] != 22232 or canonical['value'] != 9 or len(chunks) != 16 or
            accepted['bounds']['constant_copy'] != 200692 or
            accepted['bounds']['high_start'] != 22738 or
            accepted['bounds']['frames'][0]['before'] != {'low': 22484, 'high': 193210} or
            min(s['output'] for s in canonical['stages']) != 192708 or
            max(s['auxiliary'] for s in canonical['stages']) != 193209):
        raise relation.RelationError('H exact canonical/prefix allocation bounds')
    order = 'RuntimeBalanceBlindingCanonicalOrder'
    prefix = 'RuntimeBalanceBlindingWindow000TemplatePrefix'
    trace = 'RuntimeBalanceBlindingTemplateOrdinaryTrace'
    frame = 'TransferBalanceBlindingTemplateFrame'
    ns = 'RuntimeBalanceBlindingTemplateFrameBounds'
    source = f'''import ShielddSecurity.{frame}
import ShielddSecurity.GroupFixedWriteBounds
import ShielddSecurity.ScalarRandomizerWriteBounds
namespace ShielddSecurity.{ns}
set_option maxHeartbeats 250000
set_option maxRecDepth 4096

def before : GroupFixedCircuitBounds.Frame := ⟨22232,192706⟩

private theorem initial_writes : ∀ column ∈ PoseidonCompletion.writes {order}.prefix000,
    192708 ≤ column ∧ column < 193210 := by
  intro column member
  cases member
'''
    for i, chunk in enumerate(chunks):
        if not 1 <= len(chunk) <= 16:
            raise relation.RelationError('H scalar bounded chunk size')
        lower, upper = chunk[0]['output'], chunk[-1]['auxiliary'] + 1
        if not 192708 <= lower < upper <= 193210:
            raise relation.RelationError('H scalar exact bounded chunk interval')
        previous = 'initial_writes' if i == 0 else f'prefix{i:02d}_writes'
        source += f'''
private theorem chunk{i:02d}_writes :
    ∀ column ∈ PoseidonCompletion.writes {order}.chunk{i:03d},
      192708 ≤ column ∧ column < 193210 := by
  intro column member
  have bounded := ScalarRandomizerWriteBounds.writes_bounds {lower} {upper}
    {order}.chunk{i:03d} {order}.checked_bound{i:03d} column member
  omega

private theorem prefix{i+1:02d}_writes :
    ∀ column ∈ PoseidonCompletion.writes {order}.prefix{i+1:03d},
      192708 ≤ column ∧ column < 193210 := by
  intro column member
  simp only [{order}.prefix{i+1:03d}, PoseidonCompletion.writes,
    List.flatMap_append, List.mem_append] at member
  rcases member with earlier | current
  · exact {previous} column earlier
  · exact chunk{i:02d}_writes column current
'''
    source += f'''
theorem canonical_writes_outside (column : Nat)
    (covered : GroupFixedCircuitBounds.covers 22738 200692 before column) :
    column ∉ PoseidonCompletion.writes {order}.allStages := by
  intro member
  have bounded := prefix16_writes column member
  change column < 22232 ∨ (22738 ≤ column ∧ column < 192706) ∨ column = 200692 at covered
  rcases covered with low | high | copied <;> omega

private theorem mapped_writes (segments : List
    (GroupFixedCircuitCompletion.Program × GroupFixedCircuitBounds.Frame)) :
    (segments.map Prod.fst).flatMap (fun program =>
      program.stages.flatMap GroupCircuitCompletion.Step.writes) =
    segments.flatMap (fun segment =>
      segment.1.stages.flatMap GroupCircuitCompletion.Step.writes) := by
  induction segments with
  | nil => rfl
  | cons segment tail ih =>
      simp only [List.map_cons, List.flatMap_cons, ih]

theorem window_writes_outside (n column : Nat)
    (covered : GroupFixedCircuitBounds.covers 22738 200692 before column) :
    column ∉ ({frame}.programs n).flatMap (fun program =>
      program.stages.flatMap GroupCircuitCompletion.Step.writes) := by
  let segments := ({frame}.prefix n,{prefix}.after) :: {trace}.segments n
  have certified : GroupFixedCircuitBounds.Certified 22738 200692
      {prefix}.before segments := by
    have first := {prefix}.checked_bounds
      ((encodeBits 252 n)[0]?.getD false) ((encodeBits 252 n)[1]?.getD false)
    exact ⟨first.1,first.2.1,first.2.2,{trace}.certified_bounds n⟩
  have earlier := GroupFixedWriteBounds.covers_mono 22738 200692 before
    {prefix}.before (by decide) column covered
  have excluded := GroupFixedWriteBounds.certified_writes_outside 22738 200692
    {prefix}.before segments certified column earlier
  rw [← mapped_writes segments] at excluded
  simpa only [segments, List.map_cons, {frame}.programs,
    {trace}.segments_programs] using excluded

theorem owned_writes_outside (n column : Nat)
    (covered : GroupFixedCircuitBounds.covers 22738 200692 before column) :
    column ∉ {frame}.ownedWrites n := by
  intro member
  simp only [{frame}.ownedWrites, List.mem_append] at member
  rcases member with bitsOrProducts | windows
  · rcases bitsOrProducts with bits | products
    · have bitRange := List.mem_range'_1.mp bits
      change column < 22232 ∨ (22738 ≤ column ∧ column < 192706) ∨ column = 200692 at covered
      rcases covered with low | high | copied <;> omega
    · exact canonical_writes_outside column covered products
  · exact window_writes_outside n column covered windows

theorem preserves_covered {{F : Type}} [Field F] (rho : Nat → F) (n column : Nat)
    (covered : GroupFixedCircuitBounds.covers 22738 200692 before column) :
    RuntimeBalanceBlindingTemplateCanonicalPreservation.construct rho n column = rho column :=
  {frame}.outside_column rho n column (owned_writes_outside n column covered)

theorem preserves_prior {{F : Type}} [Field F] (rho : Nat → F) (n : Nat)
    (prior : List Row) (covered : GroupFixedCircuitBounds.RowsCovered 22738 200692 before prior)
    (initial : Satisfies rho prior) :
    Satisfies (RuntimeBalanceBlindingTemplateCanonicalPreservation.construct rho n) prior :=
  {frame}.preserves_rows rho n prior
    (by intro row member term present
        exact owned_writes_outside n term.1 (covered row member term present)) initial

#print axioms canonical_writes_outside
#print axioms window_writes_outside
#print axioms owned_writes_outside
#print axioms preserves_covered
#print axioms preserves_prior
end ShielddSecurity.{ns}
'''
    return ns, _signature_audits(source)
