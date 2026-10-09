"""Bounded actual reduction materializations; candidates, never qualification.

Comparator bit patches, Euclidean operand seeding and terminal endpoint/gate
joins are separate from these unconditional fresh-product constructors. The
inverse has the independently legal ownership consumer as its sole semantic
division boundary. Original rows, including a reversed assertion, are retained.
"""
from . import transfer_ivk_reduction_completion as reduction
from .generate_hash_round import linear, _signature_audits


def _rows(raw):
    return '[' + ',\n'.join('⟨'+linear(a)+','+linear(b)+'⟩' for a,b in raw) + ']'


def _product_chunk(plan, name, stages):
    if not 1 <= len(stages) <= 16:
        raise reduction.relation.RelationError('IVK reduction product chunk bound')
    copy=plan['checked']['metadata']['constant_copy']
    indices=[index for stage in stages for index in stage['rows']]
    writes=[column for stage in stages for column in (stage['output'],stage['auxiliary'])]
    kept=sorted(set(plan['readonly']) | {c for stage in stages for key in ('left','right','remainder')
        for c,_ in stage[key]} - set(writes))
    body=',\n'.join(f'.product {linear(s["left"])} {linear(s["right"])} {linear(s["remainder"])} '
        f'{s["output"]} {s["auxiliary"]}' for s in stages)
    source=f'''import ShielddSecurity.CompilerOrder
import ShielddSecurity.PoseidonCompletion
import ShielddSecurity.ScalarRandomizerCompletion
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def modulus : Nat := {reduction.relation.MODULUS}
def originalIndices : List Nat := {indices}
def rawRows : List Row := {_rows(plan['raw'][i] for i in indices)}
def kept : List Nat := {kept}
def ownedWrites : List Nat := {writes}
def stages : List CompilerCompletion.Step := [{body}]
def construct {{F : Type}} [Field F] (base : Nat → F) : Nat → F := CompilerCompletion.run base stages
theorem ordered : CompilerCompletion.Topological kept [] stages :=
  CompilerOrder.checked_order kept [] stages (by decide)
theorem products : ScalarRandomizerCompletion.Products stages := by trivial
theorem writes_exact : ∀ column, column ∈ PoseidonCompletion.writes stages ↔ column ∈ ownedWrites := by
  intro column
  simp only [PoseidonCompletion.writes,stages,ownedWrites,List.flatMap_cons,List.flatMap_nil,
    CompilerCompletion.Step.writes,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc]
theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈ CompilerCompletion.emitted stages,
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  have checked : rawRows.all (fun actual => (CompilerCompletion.emitted stages).any (fun expected =>
    decide (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∧
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp (List.all_eq_true.mp checked actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩
theorem complete {{F : Type}} [Field F] [CharP F modulus] (base : Nat → F)
    (linked : base {copy} = base 0) : Satisfies (construct base) rawRows :=
  (CompilerCompletion.original_rows_complete base stages kept rawRows {copy} ordered
    (ScalarRandomizerCompletion.products_legal base stages products) (by decide) (by decide) linked coverage).1
theorem preserves {{F : Type}} [Field F] (base : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : construct base column = base column :=
  PoseidonCompletion.run_outside base stages column (fun member => outside ((writes_exact column).mp member))
'''
    for export in ('ordered','products','writes_exact','coverage','complete','preserves'):
        source+='#print axioms '+export+'\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')


def _inverse(plan):
    p=plan['inverse'];name='RuntimeTransferIvkInverseOwnedCompletion'
    copy=plan['checked']['metadata']['constant_copy'];q,out,aux=(p[k] for k in ('quotient','product','auxiliary'))
    numerator,denominator,remainder=(linear(p[k]) for k in ('numerator','denominator','remainder'))
    source=f'''import ShielddSecurity.GroupRowCompletion
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
namespace ShielddSecurity.{name}
def modulus : Nat := {reduction.relation.MODULUS}
def numerator : Linear := {numerator}
def denominator : Linear := {denominator}
def remainder : Linear := {remainder}
def originalIndices : List Nat := {p['rows']}
def rawRows : List Row := {_rows(plan['raw'][i] for i in p['rows'])}
def expectedRows : List Row := GroupRowCompletion.quotientRows numerator denominator remainder {q} {out} {aux}
def ownedWrites : List Nat := GroupRowCompletion.writes {q} {out} {aux}
def construct {{F : Type}} [Field F] (base : Nat → F) : Nat → F :=
  GroupRowCompletion.extendQuotient base numerator denominator remainder {q} {out} {aux}
theorem fresh : ∀ term ∈ numerator ++ denominator ++ remainder, term.1 ∉ ownedWrites := by
  have checked : (numerator ++ denominator ++ remainder).all (fun term => decide (term.1 ∉ ownedWrites)) = true := by decide
  intro term member
  exact of_decide_eq_true (List.all_eq_true.mp checked term member)
theorem coverage : ∀ actual ∈ rawRows, ∃ expected ∈ expectedRows,
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b := by
  have checked : rawRows.all (fun actual => expectedRows.any (fun expected => decide (
    (Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus expected.a ∨
      Compiler.canonical modulus (Compiler.unoutline {copy} actual.a) = Compiler.canonical modulus (scaleLinear (-1) expected.a)) ∧
    Compiler.canonical modulus (Compiler.unoutline {copy} actual.b) = Compiler.canonical modulus expected.b))) = true := by decide
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp (List.all_eq_true.mp checked actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩
theorem preserves {{F : Type}} [Field F] (base : Nat → F) (column : Nat)
    (outside : column ∉ ownedWrites) : construct base column = base column :=
  GroupRowCompletion.extend_preserves base numerator denominator remainder {q} {out} {aux} column outside
theorem complete {{F : Type}} [Field F] [CharP F modulus] (base : Nat → F)
    (linked : base {copy} = base 0) (legal : eval base denominator ≠ 0) :
    Satisfies (construct base) rawRows := by
  have completed := GroupRowCompletion.extend_complete base numerator denominator remainder {q} {out} {aux}
    (by decide) (by decide) (by decide) fresh legal
  have copyLink : construct base {copy} = construct base 0 := by
    rw [preserves base {copy} (by decide),preserves base 0 (by decide),linked]
  intro actual member
  obtain ⟨expected,present,left,right⟩ := coverage actual member
  have sound : Square (eval (construct base) expected.a) (eval (construct base) expected.b) := completed expected present
  rcases left with positive | negative
  · rw [← Compiler.canonical_equal (construct base) _ _ positive,
      ← Compiler.canonical_equal (construct base) _ _ right] at sound
    simpa only [Compiler.eval_unoutline (construct base) {copy} _ copyLink] using sound
  · have negated : Square (eval (construct base) (scaleLinear (-1) expected.a))
        (eval (construct base) expected.b) := by simpa [Square,eval_scale] using sound
    rw [← Compiler.canonical_equal (construct base) _ _ negative,
      ← Compiler.canonical_equal (construct base) _ _ right] at negated
    simpa only [Compiler.eval_unoutline (construct base) {copy} _ copyLink] using negated
'''
    for export in ('fresh','coverage','preserves','complete'):source+='#print axioms '+export+'\n'
    return name,_signature_audits(source+f'end ShielddSecurity.{name}\n')


def generate(data, accepted_ivk, extracted, expected_relation, readonly_lcs=()):
    """Emit34 bounded product chunks and the actual3-write inverse candidate.

    These constructors establish all1012 comparator/gate materialization rows
    plus3 inverse rows. The256 Boolean rows, reconstructed q/r, independently
    derived endpoints/hash equality/gate assertion and copy join remain open.
    """
    p=reduction.plan(data,accepted_ivk,extracted,expected_relation,readonly_lcs)
    for phase in p['phases']:
        for index,start in enumerate(range(0,len(phase['stages']),16)):
            name=f'RuntimeTransferIvkComparison{phase["phase"]}OwnedChunk{index}'
            yield _product_chunk(p,name,phase['stages'][start:start+16])
    yield _product_chunk(p,'RuntimeTransferIvkTerminalGateOwnedCompletion',[p['gate_stage']])
    yield _inverse(p)
