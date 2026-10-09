import ShielddSecurity.TransferSem
import ShielddSecurity.RoutingTagSemantics
import ShielddSecurity.RoutingLowWord
import ShielddSecurity.RoutingBitSemantics

set_option maxHeartbeats 400000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferRoutingBranchCompletion
open TransferSem TransferCore

structure LegalRoutingInputs where
  regulatedPrecision : Nat
  unregulatedPrecision : Nat
  height : Nat
  ordered : regulatedPrecision ≤ unregulatedPrecision
  bounded : unregulatedPrecision ≤ 32

def precision (base : TransferSem.Witness) (i : LegalRoutingInputs) : Nat :=
  if base.regulated then i.regulatedPrecision else i.unregulatedPrecision

def swapped (c : Crypto) (base : TransferSem.Witness) : Bool :=
  decide (c.hash .routePermutation [base.nonce] % 2 = 1)

def senderSlot (c : Crypto) (base : TransferSem.Witness) (slot : Fin 2) : Bool :=
  decide (if swapped c base then slot.val = 1 else slot.val = 0)

def meaningful (c : Crypto) (base : TransferSem.Witness) (slot : Fin 2) : Bool :=
  !senderSlot c base slot || base.regulated || (base.outputs 1).amount != 0

def routeWord (c : Crypto) (base : TransferSem.Witness) (slot : Fin 2) : Nat :=
  c.hash .route (pointFields (if senderSlot c base slot then
    base.sender.address.transmission else base.receiver.address.transmission))

def randomWord (c : Crypto) (base : TransferSem.Witness) (slot : Fin 2) : Nat :=
  c.hash .routeRandomness [base.nonce,slot.val]

def selectedWord (c : Crypto) (base : TransferSem.Witness) (i : LegalRoutingInputs)
    (slot : Fin 2) (index : Nat) : Nat :=
  if meaningful c base slot && decide (index < precision base i)
    then routeWord c base slot else randomWord c base slot

def bits (c : Crypto) (base : TransferSem.Witness) (i : LegalRoutingInputs)
    (slot : Fin 2) : List Bool :=
  (List.range 32).map fun index => decide (selectedWord c base i slot index / 2^index % 2 = 1)

def construct (c : Crypto) (base : TransferSem.Witness) (i : LegalRoutingInputs) : Routing :=
  { regulatedPrecision := i.regulatedPrecision
    unregulatedPrecision := i.unregulatedPrecision
    height := i.height
    parameterSet := c.hash .routeParameters [i.regulatedPrecision,i.unregulatedPrecision,i.height]
    tags := fun slot => binary (bits c base i slot) }

theorem bit_digit_exact (n index : Nat) :
    (if decide (n / 2^index % 2 = 1) then 1 else 0) = n / 2^index % 2 := by
  by_cases one : n / 2^index % 2 = 1
  · simp [one]
  · have bound := Nat.mod_lt (n / 2^index) (by decide : 0 < 2)
    have zero : n / 2^index % 2 = 0 := by omega
    simp [zero]

theorem bits_length (c : Crypto) (base : TransferSem.Witness) (i : LegalRoutingInputs)
    (slot : Fin 2) : (bits c base i slot).length = 32 := by
  simp [bits]

theorem bits_index (c : Crypto) (base : TransferSem.Witness) (i : LegalRoutingInputs)
    (slot : Fin 2) (index : Fin 32) :
    (bits c base i slot).getD index.val false =
      decide (selectedWord c base i slot index.val / 2^index.val % 2 = 1) := by
  simp only [bits, List.getD_eq_getElem?_getD, List.getElem?_map]
  have within : index.val < (List.range 32).length := by simp
  rw [List.getElem?_eq_getElem within]
  simp

theorem constructed_tag_bound (c : Crypto) (base : TransferSem.Witness) (i : LegalRoutingInputs)
    (slot : Fin 2) : (construct c base i).tags slot < 2^32 := by
  simpa only [construct, bits_length] using binary_bound (bits c base i slot)

theorem constructed_tag_bits (c : Crypto) (base : TransferSem.Witness) (i : LegalRoutingInputs)
    (slot : Fin 2) (index : Fin 32) :
    (construct c base i).tags slot / 2^index.val % 2 =
      selectedWord c base i slot index.val / 2^index.val % 2 := by
  change binary (bits c base i slot) / 2^index.val % 2 = _
  rw [RoutingTagSemantics.binary_bit, bits_index]
  exact bit_digit_exact _ _

theorem constructed_routing_semantics (c : Crypto) (base : TransferSem.Witness)
    (i : LegalRoutingInputs) : RoutingSem c {base with routing := construct c base i} := by
  change i.regulatedPrecision ≤ i.unregulatedPrecision ∧ i.unregulatedPrecision ≤ 32 ∧
    (construct c base i).parameterSet =
      c.hash .routeParameters [i.regulatedPrecision,i.unregulatedPrecision,i.height] ∧
    ∀ slot : Fin 2, (construct c base i).tags slot < 2^32 ∧
      ∀ index : Fin 32, (construct c base i).tags slot / 2^index.val % 2 =
        selectedWord c base i slot index.val / 2^index.val % 2
  exact ⟨i.ordered,i.bounded,rfl,fun slot =>
    ⟨constructed_tag_bound c base i slot,constructed_tag_bits c base i slot⟩⟩

theorem restore_full_record (c : Crypto) (base : TransferSem.Witness)
    (i : LegalRoutingInputs) :
    {{base with routing := construct c base i} with routing := base.routing} = base := by
  cases base
  rfl

def routingFields (r : Routing) : List Nat :=
  [r.regulatedPrecision,r.unregulatedPrecision,r.height,r.parameterSet,r.tags 0,r.tags 1]

theorem canonical_constructed_routing_fields (c : Crypto) (base : TransferSem.Witness)
    (i : LegalRoutingInputs) (cryptoCanonical : CanonicalCrypto c)
    (heightCanonical : i.height < fieldModulus) :
    fieldsCanonical (routingFields (construct c base i)) := by
  have smallField : 32 < fieldModulus := by decide
  have wordField : 2^32 < fieldModulus := by decide
  have regulatedBound : i.regulatedPrecision < fieldModulus :=
    Nat.lt_of_le_of_lt (i.ordered.trans i.bounded) smallField
  have unregulatedBound : i.unregulatedPrecision < fieldModulus :=
    Nat.lt_of_le_of_lt i.bounded smallField
  have tagCanonical : ∀ slot : Fin 2, (construct c base i).tags slot < fieldModulus :=
    fun slot => Nat.lt_trans (constructed_tag_bound c base i slot) wordField
  simp only [fieldsCanonical,routingFields,List.mem_cons,List.not_mem_nil,
    forall_eq_or_imp,false_implies,forall_const,and_true]
  exact ⟨regulatedBound,unregulatedBound,heightCanonical,cryptoCanonical.1 _ _,
    tagCanonical 0,tagCanonical 1⟩

theorem fieldsCanonical_append (a b : List Nat) :
    fieldsCanonical (a ++ b) ↔ fieldsCanonical a ∧ fieldsCanonical b := by
  simp only [fieldsCanonical,List.mem_append,or_imp,forall_and]

-- The first twelve scalar fields precede routing in CanonicalWitness. The
-- other structured blocks are preserved by the full-record routing update.
def canonicalHeader (w : TransferSem.Witness) : List Nat :=
  [w.anchor,w.assetAnchor,w.userAnchor,w.asset,w.timestamp,w.nonce,w.blinding,
    w.paddingSeed,w.auth.nk,w.auth.ivk,w.auth.quotient,w.auth.randomizer]

theorem canonical_witness_preserved (c : Crypto) (base : TransferSem.Witness)
    (i : LegalRoutingInputs) (baseCanonical : CanonicalWitness base)
    (cryptoCanonical : CanonicalCrypto c) (heightCanonical : i.height < fieldModulus) :
    CanonicalWitness {base with routing := construct c base i} := by
  have routingCanonical := canonical_constructed_routing_fields c base i cryptoCanonical heightCanonical
  simp only [CanonicalWitness,fieldsCanonical_append] at baseCanonical ⊢
  rcases baseCanonical with
    ⟨⟨⟨⟨⟨⟨⟨⟨header,ak⟩,rk⟩,registry⟩,sender⟩,receiver⟩,notes⟩,volume⟩,encryption⟩
  have oldHeader : fieldsCanonical (canonicalHeader base ++ routingFields base.routing) := header
  have common := (fieldsCanonical_append _ _).mp oldHeader
  have newHeader := (fieldsCanonical_append _ _).mpr ⟨common.1,routingCanonical⟩
  exact ⟨⟨⟨⟨⟨⟨⟨⟨newHeader,ak⟩,rk⟩,registry⟩,sender⟩,receiver⟩,notes⟩,volume⟩,encryption⟩

theorem constructed_canonical_routing_semantics (c : Crypto) (base : TransferSem.Witness)
    (i : LegalRoutingInputs) (baseCanonical : CanonicalWitness base)
    (cryptoCanonical : CanonicalCrypto c) (heightCanonical : i.height < fieldModulus) :
    CanonicalWitness {base with routing := construct c base i} ∧
    RoutingSem c {base with routing := construct c base i} := by
  exact ⟨canonical_witness_preserved c base i baseCanonical cryptoCanonical heightCanonical,
    constructed_routing_semantics c base i⟩

theorem refuse_parameter_mutation (c : Crypto) (base : TransferSem.Witness)
    (i : LegalRoutingInputs) (bad : Nat)
    (changed : bad ≠ c.hash .routeParameters [i.regulatedPrecision,i.unregulatedPrecision,i.height]) :
    ¬ RoutingSem c {base with routing := {construct c base i with parameterSet := bad}} := by
  intro invalid
  exact changed invalid.2.2.1

theorem refuse_reversed_precisions (c : Crypto) (base : TransferSem.Witness)
    (i : LegalRoutingInputs) (bad : Nat) (reversed : i.unregulatedPrecision < bad) :
    ¬ RoutingSem c {base with routing := {construct c base i with regulatedPrecision := bad}} := by
  intro invalid
  exact Nat.not_le_of_gt reversed invalid.1

theorem refuse_unregulated_above32 (c : Crypto) (base : TransferSem.Witness)
    (i : LegalRoutingInputs) (bad : Nat) (overflow : 32 < bad) :
    ¬ RoutingSem c {base with routing := {construct c base i with unregulatedPrecision := bad}} := by
  intro invalid
  exact Nat.not_le_of_gt overflow invalid.2.1

theorem refuse_tag_overflow (c : Crypto) (base : TransferSem.Witness)
    (i : LegalRoutingInputs) (slot : Fin 2) (bad : Nat) (overflow : 2^32 ≤ bad) :
    ¬ RoutingSem c {base with routing := {construct c base i with
      tags := fun s => if s = slot then bad else (construct c base i).tags s}} := by
  intro invalid
  have bound := (invalid.2.2.2 slot).1
  simp only at bound
  exact Nat.not_lt_of_ge overflow bound

theorem refuse_tag_bit_mutation (c : Crypto) (base : TransferSem.Witness)
    (i : LegalRoutingInputs) (slot : Fin 2) (index : Fin 32) (bad : Nat)
    (changed : bad/2^index.val%2 ≠ selectedWord c base i slot index.val/2^index.val%2) :
    ¬ RoutingSem c {base with routing := {construct c base i with
      tags := fun s => if s = slot then bad else (construct c base i).tags s}} := by
  intro invalid
  have digit := (invalid.2.2.2 slot).2 index
  simp only at digit
  exact changed digit

#print axioms refuse_parameter_mutation
#print axioms refuse_reversed_precisions
#print axioms refuse_unregulated_above32
#print axioms refuse_tag_overflow
#print axioms refuse_tag_bit_mutation

#print axioms canonical_constructed_routing_fields
#print axioms fieldsCanonical_append
#print axioms canonical_witness_preserved
#print axioms constructed_canonical_routing_semantics

#print axioms bit_digit_exact
#print axioms bits_length
#print axioms bits_index
#print axioms constructed_tag_bound
#print axioms constructed_tag_bits
#print axioms constructed_routing_semantics
#print axioms restore_full_record
end ShielddSecurity.TransferRoutingBranchCompletion
