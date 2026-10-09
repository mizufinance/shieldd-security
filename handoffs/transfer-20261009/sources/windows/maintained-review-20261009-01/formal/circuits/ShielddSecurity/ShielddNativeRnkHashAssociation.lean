import ShielddSecurity.ShielddNativeRnkHash
import ShielddSecurity.ShielddNativeActionWitnessAssociation

set_option maxHeartbeats 200000

namespace ShielddSecurity.ShielddNativeRnkHashAssociation

open ShielddNativeAddress

variable {F : Type} [Field F]
  {E S R K Q Signing J : Type} [AddCommGroup J]
  {fq : GroupNativeSdk.FqBytes Q} {fr : GroupNativeSdk.FrBytes R}
  {d : F} {model : Group.StandardCurveModel J d}

/-- Successful execution of the same owned ActionWitness sequence instantiates
its commitment callback with the actual SMALL/domain18 arithmetic program.
The stored commitment is an original sender field, never chosen from the key.
No Poseidon injectivity or probabilistic property is used. -/
theorem registered_commitment [DecidableEq S] [DecidableEq Q] {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream)
    (agreement : Secret → S → Option GroupByteCodec.Bytes)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (codec : TransferReduction.CanonicalField F)
    (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
    (secret : Secret) (walletNk : Q)
    (source : ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key) (key : Q)
    (regulated : source.regulated = true)
    (accepted : ShielddNativeActionWitnessAssociation.nullifierKey upstream primitives agreement
      (ShielddNativeRnkHash.hash fq arithmetic initial square codec small wide)
      secret walletNk source = some key) :
    Poseidon.hash3 small 18 [(fq.integer key : F)] = (fq.integer source.sender.registered : F) := by
  obtain ⟨_,_,_,matching,_,_⟩ := ShielddNativeActionWitnessAssociation.accepted_regulated
    upstream primitives agreement (ShielddNativeRnkHash.hash fq arithmetic initial square codec small wide)
    secret walletNk source key regulated accepted
  have fields := congrArg (ShielddNativeIvkHash.fqValue (F := F) fq) matching
  rw [ShielddNativeRnkHash.callback_commitment fq arithmetic initial square codec small wide,
    ShielddNativeRnkHash.commitment_value fq arithmetic initial square codec small] at fields
  exact fields

/-- This difference equation concerns the registered source seed before row
completion. The independently derived native hash equation discharges its
stored field; actual compiler LC1528 and completion preservation stay in the
existing generated seed/row consumers. -/
theorem registered_seed [DecidableEq S] [DecidableEq Q] {Routes Origin Key : Type}
    (upstream : ShielddNativeSdk.Upstream E S R K Q Signing J fq fr d model)
    (primitives : Primitives upstream)
    (agreement : Secret → S → Option GroupByteCodec.Bytes)
    (arithmetic : ShielddNativeIvkHash.FqArithmetic (F := F) Q fq)
    (initial : ShielddNativeIvkSource.SdkInitial fq arithmetic)
    (square : ShielddNativeIvkSdkProgram.SquarePrimitive (F := F) fq)
    (codec : TransferReduction.CanonicalField F)
    (small : Poseidon.Parameters F 3) (wide : Poseidon.Parameters F 6)
    (secret : Secret) (walletNk : Q)
    (source : ShielddNativeActionWitnessAssociation.Source S Q Routes Origin Key) (key : Q)
    (registeredColumn regulatedColumn : Nat) (base : Nat → F)
    (distinct : registeredColumn ≠ regulatedColumn)
    (regulated : source.regulated = true)
    (accepted : ShielddNativeActionWitnessAssociation.nullifierKey upstream primitives agreement
      (ShielddNativeRnkHash.hash fq arithmetic initial square codec small wide)
      secret walletNk source = some key) :
    Poseidon.hash3 small 18 [(fq.integer key : F)] -
      ShielddNativeActionWitnessAssociation.sourceSeed fq registeredColumn regulatedColumn source base registeredColumn = 0 := by
  rw [ShielddNativeActionWitnessAssociation.source_seed_registered registeredColumn regulatedColumn source base distinct,
    registered_commitment upstream primitives agreement arithmetic initial square codec small wide
      secret walletNk source key regulated accepted]
  exact sub_self _

set_option pp.all true in
#check @registered_commitment
#print axioms registered_commitment
set_option pp.all true in
#check @registered_seed
#print axioms registered_seed

end ShielddSecurity.ShielddNativeRnkHashAssociation
