"""Actual H write separation from small scalar chunks and symbolic window bounds."""
from . import transfer_balance_blinding_program as whole, transfer_relation as relation
from .generate_hash_round import _signature_audits


def generate(parent, pages, expected_base, expected_blinding, extracted, *, readonly_lcs=()):
    accepted = whole.plan(parent, pages, expected_base, expected_blinding, extracted, readonly_lcs)
    canonical = accepted['canonical']
    chunks = canonical['chunks']
    if (canonical['bit_start'] != 22232 or canonical['value'] != 9 or len(chunks) != 16 or
            accepted['bounds']['constant_copy'] != 200692 or
            accepted['bounds']['high_start'] != 192708 or
            accepted['bounds']['frames'][0]['before'] != {'low': 22484, 'high': 193210} or
            min(s['output'] for s in canonical['stages']) != 192708 or
            max(s['auxiliary'] for s in canonical['stages']) != 193209):
        raise relation.RelationError('H exact canonical/prefix allocation bounds')
    order = 'RuntimeBalanceBlindingCanonicalOrder'
    prefix = 'RuntimeBalanceBlindingWindow000TemplatePrefix'
    trace = 'RuntimeBalanceBlindingTemplateOrdinaryTrace'
    frame = 'TransferBalanceBlindingTemplateFrame'
    ns = 'RuntimeBalanceBlindingTemplateFrameBounds'
    source = f'''{''.join(f'import ShielddSecurity.RuntimeBalanceBlindingTemplatePage{i:02d}WideBounds'+chr(10) for i in range(8))}import ShielddSecurity.{frame}
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

private theorem ordinary_wide_bounds (n : Nat) :
    GroupFixedCircuitBounds.Certified 22738 200692
      RuntimeBalanceBlindingWindow001TemplateTrace.before ({trace}.segments n) := by
  apply GroupFixedTemplatePages.certified_pages
  refine ⟨RuntimeBalanceBlindingTemplatePage00WideBounds.certified_bounds n, ?_⟩
  refine ⟨RuntimeBalanceBlindingTemplatePage01WideBounds.certified_bounds n, ?_⟩
  refine ⟨RuntimeBalanceBlindingTemplatePage02WideBounds.certified_bounds n, ?_⟩
  refine ⟨RuntimeBalanceBlindingTemplatePage03WideBounds.certified_bounds n, ?_⟩
  refine ⟨RuntimeBalanceBlindingTemplatePage04WideBounds.certified_bounds n, ?_⟩
  refine ⟨RuntimeBalanceBlindingTemplatePage05WideBounds.certified_bounds n, ?_⟩
  refine ⟨RuntimeBalanceBlindingTemplatePage06WideBounds.certified_bounds n, ?_⟩
  refine ⟨RuntimeBalanceBlindingTemplatePage07WideBounds.certified_bounds n, ?_⟩
  trivial

theorem window_writes_outside (n column : Nat)
    (covered : GroupFixedCircuitBounds.covers 22738 200692 before column) :
    column ∉ ({frame}.programs n).flatMap (fun program =>
      program.stages.flatMap GroupCircuitCompletion.Step.writes) := by
  let segments := ({frame}.prefixProgram n,{prefix}.after) :: {trace}.segments n
  have certified : GroupFixedCircuitBounds.Certified 22738 200692
      {prefix}.before segments := by
    have first := RuntimeBalanceBlindingTemplatePage00WideBounds.prefix_bounds
      ((encodeBits 252 n)[0]?.getD false) ((encodeBits 252 n)[1]?.getD false)
    exact ⟨first.1,first.2.1,first.2.2,ordinary_wide_bounds n⟩
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


def generate_modules(parent, pages, expected_base, expected_blinding, extracted, *, readonly_lcs=()):
    accepted = whole.plan(parent, pages, expected_base, expected_blinding, extracted, readonly_lcs)
    if accepted['bounds']['high_start'] != 192708 or len(accepted['loop']['programs']) != 126:
        raise relation.RelationError('H exact source allocation before wider prior-row preservation')
    modules=[]
    for page in range(8):
        first=max(1,16*page); last=min(126,16*(page+1))
        indices=list(range(first,last))
        ns=f'RuntimeBalanceBlindingTemplatePage{page:02d}WideBounds'
        trace=f'RuntimeBalanceBlindingTemplatePage{page:02d}Trace'
        body=f'import ShielddSecurity.{trace}\n'
        if page==0: body+='import ShielddSecurity.RuntimeBalanceBlindingWindow000TemplatePrefix\n'
        body+=f'namespace ShielddSecurity.{ns}\nset_option maxHeartbeats 300000\nset_option maxRecDepth 4096\n'
        if page==0:
            p='RuntimeBalanceBlindingWindow000TemplatePrefix'
            body+=f"""
theorem prefix_bounds (low high : Bool) :
    ({p}.before.low ≤ {p}.after.low ∧ {p}.before.high ≤ {p}.after.high) ∧
      GroupFixedCircuitBounds.RowsCovered 22738 200692 {p}.after ({p}.program low high).rows ∧
      GroupFixedCircuitBounds.WritesOutside 22738 200692 {p}.before ({p}.program low high) :=
  GroupFixedCircuitBounds.checked_local 22738 200692 {p}.before {p}.after ({p}.program low high) (by
    change GroupFixedCircuitBounds.checkLocal 22738 200692 {p}.before {p}.after ({p}.program false false) = true
    decide)
#print axioms prefix_bounds
"""
        for i in indices:
            w=f'RuntimeBalanceBlindingWindow{i:03d}TemplateTrace'
            body+=f"""
private theorem bound{i:03d} (low high : Bool) :
    ({w}.before.low ≤ {w}.after.low ∧ {w}.before.high ≤ {w}.after.high) ∧
      GroupFixedCircuitBounds.RowsCovered 22738 200692 {w}.after ({w}.window low high).program.rows ∧
      GroupFixedCircuitBounds.WritesOutside 22738 200692 {w}.before ({w}.window low high).program :=
  GroupFixedCircuitBounds.checked_local 22738 200692 {w}.before {w}.after ({w}.window low high).program (by
    change GroupFixedCircuitBounds.checkLocal 22738 200692 {w}.before {w}.after ({w}.window false false).program = true
    decide)
"""
        w=f'RuntimeBalanceBlindingWindow{first:03d}TemplateTrace'
        body+=f"""
theorem certified_bounds (n : Nat) : GroupFixedCircuitBounds.Certified 22738 200692
    {w}.before ({trace}.segments n) := by
"""
        for i in indices:
            body+=f'  have bounded{i} := bound{i:03d} ((encodeBits 252 n)[{2*i}]?.getD false) ((encodeBits 252 n)[{2*i+1}]?.getD false)\n'
            body+=f'  refine ⟨bounded{i}.1,bounded{i}.2.1,bounded{i}.2.2,?_⟩\n'
        body+='  trivial\n#print axioms certified_bounds\n'
        body+=f'end ShielddSecurity.{ns}\n'
        modules.append((ns,_signature_audits(body)))
    modules.append(generate(parent,pages,expected_base,expected_blinding,extracted,readonly_lcs=readonly_lcs))
    return modules
