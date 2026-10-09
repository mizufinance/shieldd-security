"""Actual typed registered/selector LC seed; no row or native qualification."""
from . import transfer_authorization_join as caller
from .transfer_relation import RelationError


def generate(checked, ring_selection, registry_point):
    """Consume accepted caller parser output and existing accepted component LCs.

    The caller must retain the original ingress/capture identities. This
    producer rechecks structural/shared LCs, then emits source-field assignment
    consequences only. It neither replays ordinary rows nor certifies Rust
    object/codec meaning or native hash-to-compiled Poseidon correspondence.
    """
    try:
        selected = caller.inspect_join(checked, ring_selection, registry_point)
        obj = checked['metadata']
        values = selected['values']
        if (obj['caller']['registered_rnk'] != {'source': [1, 1525]} or
                obj['caller']['regulated'] != {'source': [1, 7]} or
                values['registered_rnk'] != ((1528, 1),) or
                values['regulated'] != ((10, 1),)):
            raise RelationError('actual registered/regulated source LC mismatch')
    except (KeyError, TypeError) as error:
        raise RelationError('accepted registered-source role shape required') from error
    name = 'RuntimeNativeRegisteredSeed'
    source = '''import ShielddSecurity.ShielddNativeActionWitnessAssociation
import ShielddSecurity.Rows
set_option maxHeartbeats 250000
namespace ShielddSecurity.RuntimeNativeRegisteredSeed
open ShielddNativeAddress
variable {F : Type} [Field F]
  {E S R K Q Signing J Routes Origin Key : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

-- Actual captured SourceWitness aliases, independently checked one by one.
-- These typed aliases identify LCs; the source object/codec relation is separate.
def registeredSource : Nat × Nat := (1,1525)
def regulatedSource : Nat × Nat := (1,7)
def registered : Linear := [(1528,1)]
def regulated : Linear := [(10,1)]

def sourceAssignment (source : ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key) (base : Nat → F) : Nat → F :=
  ShielddNativeActionWitnessAssociation.sourceSeed fq 1528 10 source base

theorem registered_source_seed (source : ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key) (base : Nat → F) :
    eval (sourceAssignment (fq := fq) source base) registered =
      (fq.integer source.sender.registered : F) := by
  simpa only [registered,eval,Int.cast_one,one_mul,add_zero,sourceAssignment] using
    ShielddNativeActionWitnessAssociation.source_seed_registered (fq := fq) 1528 10 source base (by decide)

theorem regulated_source_seed (source : ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key) (base : Nat → F) :
    eval (sourceAssignment (fq := fq) source base) regulated =
      (if source.regulated then (1 : F) else 0) := by
  simpa only [regulated,eval,Int.cast_one,one_mul,add_zero,sourceAssignment] using
    ShielddNativeActionWitnessAssociation.source_seed_regulated (fq := fq) 1528 10 source base

theorem registered_source_gate [DecidableEq S] [DecidableEq Q]
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream)
    (agreement : Secret → S → Option GroupByteCodec.Bytes) (hash : Nat → List Q → Q)
    (secret : Secret) (walletNk : Q) (source : ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key) (key : Q)
    (accepted : ShielddNativeActionWitnessAssociation.nullifierKey upstream primitives agreement hash secret walletNk source = some key)
    (base : Nat → F) :
    eval (sourceAssignment (fq := fq) source base) regulated *
      ((fq.integer (hash 18 [key]) : F) -
        eval (sourceAssignment (fq := fq) source base) registered) = 0 := by
  rw [registered_source_seed,regulated_source_seed]
  have gate := ShielddNativeActionWitnessAssociation.source_seed_gate upstream primitives agreement hash secret walletNk
    source key accepted 1528 10 base (by decide)
  rw [ShielddNativeActionWitnessAssociation.source_seed_registered 1528 10 source base (by decide),ShielddNativeActionWitnessAssociation.source_seed_regulated] at gate
  exact gate

theorem other_columns_preserved (source : ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key)
    (base : Nat → F) (column : Nat) (other : column ∉ [1528,10]) :
    sourceAssignment (fq := fq) source base column = base column := by
  apply ShielddNativeActionWitnessAssociation.source_seed_preserves
  · intro same; apply other; simp only [List.mem_cons,List.not_mem_nil,or_false]; exact Or.inl same
  · intro same; apply other; simp only [List.mem_cons,List.not_mem_nil,or_false]; exact Or.inr same

'''
    for export in ('registered_source_seed', 'regulated_source_seed',
                   'registered_source_gate', 'other_columns_preserved'):
        source += 'set_option pp.all true in\n#check @' + export + '\n#print axioms ' + export + '\n'
    return name, source + 'end ShielddSecurity.RuntimeNativeRegisteredSeed\n'
