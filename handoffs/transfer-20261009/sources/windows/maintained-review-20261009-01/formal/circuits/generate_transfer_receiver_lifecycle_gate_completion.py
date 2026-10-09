"""Construct each captured lifecycle product from legal encoded status bits."""
import ast
import re
from . import transfer_relation as relation
from .generate_hash_round import linear, _signature_audits


def generate(gate_source, index):
    index = relation.natural(index, 131)
    if index not in (0, 1, 2, *range(67, 131)):
        raise relation.RelationError('captured receiver lifecycle gate required')
    gate = f'RuntimeTransferReceiverLifecycleGate{index:03}'
    if f'namespace ShielddSecurity.{gate}\n' not in gate_source:
        raise relation.RelationError('exact physical gate namespace required')
    def captured(name):
        match = re.search(r'^def ' + name + r' : Linear := (\[[^\n]+\])$', gate_source, re.M)
        if match is None:
            raise relation.RelationError('closed physical operand required')
        terms = ast.literal_eval(re.sub(r'\((-?\d+) : Int\)', r'\1', match[1]))
        if match[1] != linear(terms):
            raise relation.RelationError('exact captured linear spelling required')
        return terms
    left, right = captured('left'), captured('right')
    flag = [(10, 1)]
    bit = [(0, -1), (1849 + index, 1)] if index == 0 else [(1849 + index, 1)]
    if sorted((left, right)) != sorted((flag, bit)):
        raise relation.RelationError('exact constrained receiver bit required')
    output, auxiliary = captured('output'), captured('auxiliary')
    if len(output) != 1 or len(auxiliary) != 1 or output[0][1] != 1 or auxiliary[0][1] != 1:
        raise relation.RelationError('unit physical product pivots required')
    out, aux = output[0][0], auxiliary[0][0]
    if out == aux or {out, aux} & {0, 10, 200692, *range(1849, 1980)}:
        raise relation.RelationError('product writes must be fresh for receiver word and inputs')
    name = f'TransferReceiverLifecycleGateCompletion{index:03}'
    text = f'''import ShielddSecurity.{gate}
import ShielddSecurity.ReceiverLifecycleProductCompletion
namespace ShielddSecurity.{name}
set_option maxHeartbeats 200000

def writes : List Nat := [{out},{aux}]
def expectedRows : List Row :=
  ReceiverLifecycleProductCompletion.materializedRows {gate}.left {gate}.right {out} {aux} ++
    [⟨[],[]⟩]
def completed {{F : Type}} [Field F] (base : Nat → F) : Nat → F :=
  ScalarCompletion.extendProduct base {gate}.left {gate}.right [] {out} {aux}

theorem preserved {{F : Type}} [Field F] (base : Nat → F) (column : Nat)
    (outside : column ∉ writes) : completed base column = base column :=
  ReceiverLifecycleProductCompletion.materialized_preserves base _ _ _ _ column outside

theorem coverage : ∀ actual ∈ {gate}.rawRows,∃ expected ∈ expectedRows,
    Compiler.canonical {gate}.modulus (Compiler.unoutline 200692 actual.a) = Compiler.canonical {gate}.modulus expected.a ∧
    Compiler.canonical {gate}.modulus (Compiler.unoutline 200692 actual.b) = Compiler.canonical {gate}.modulus expected.b := by
  have certificate : {gate}.rawRows.all (fun actual => expectedRows.any (fun expected => decide
    (Compiler.canonical {gate}.modulus (Compiler.unoutline 200692 actual.a) = Compiler.canonical {gate}.modulus expected.a ∧
     Compiler.canonical {gate}.modulus (Compiler.unoutline 200692 actual.b) = Compiler.canonical {gate}.modulus expected.b))) = true := by decide
  intro actual member
  obtain ⟨expected,present,equations⟩ := List.any_eq_true.mp ((List.all_eq_true.mp certificate) actual member)
  exact ⟨expected,present,of_decide_eq_true equations⟩

theorem complete {{F : Type}} [Field F] [CharP F {gate}.modulus]
    (base : Nat → F) (one : base 0 = 1) (linked : base 200692 = base 0)
    (n : Nat) (flag : Bool) (flagValue : base 10 = if flag then 1 else 0)
    (bitValue : base {1849 + index} = if (encodeBits 131 n)[{index}]?.getD false then 1 else 0)
    (legal : flag = true → ReceiverLifecycle.LegalActive n) :
    Satisfies (completed base) {gate}.rawRows := by
  have zeroProduct : eval base {gate}.left * eval base {gate}.right = 0 := by
    simpa [{gate}.left,{gate}.right,eval,one,flagValue,bitValue,mul_comm] using
      (ReceiverLifecycle.enabled_product (F := F) n {index} flag (by decide) legal)
  have built := ReceiverLifecycleProductCompletion.materialized_zero base {gate}.left {gate}.right {out} {aux}
    (by decide) (by decide) zeroProduct
  have copyLink : completed base 200692 = completed base 0 := by
    rw [preserved base 200692 (by decide),preserved base 0 (by decide),linked]
  have expected : Satisfies (completed base) expectedRows := by
    intro row member
    rcases List.mem_append.mp member with product | link
    · exact built.1 row product
    · simp only [List.mem_singleton] at link
      subst row
      simp [Square,eval]
  intro actual member
  obtain ⟨row,present,left,right⟩ := coverage actual member
  have result : Square (eval (completed base) row.a) (eval (completed base) row.b) := expected row present
  rw [← Compiler.canonical_equal (completed base) _ _ left,
    ← Compiler.canonical_equal (completed base) _ _ right] at result
  simpa only [Compiler.eval_unoutline (completed base) 200692 _ copyLink] using result

#print axioms preserved
#print axioms coverage
#print axioms complete
end ShielddSecurity.{name}
'''
    return name, _signature_audits(text)
