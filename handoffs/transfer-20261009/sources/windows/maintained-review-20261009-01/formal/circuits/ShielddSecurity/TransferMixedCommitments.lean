import ShielddSecurity.TransferMixedBody
import ShielddSecurity.TransferBalanceGroup

set_option maxHeartbeats 150000

namespace ShielddSecurity.TransferMixedCommitments

open TransferMixedBody TransferBalanceGroup TransferConservation

/-!
Complete-source association for the native mixed-action commitment loop.
Stored points are independent of extracted openings. Their equality is a local
per-family interpretation interface, not a supplied whole-key conservation fact.
Transfer, Reshape and Withdrawal require their own exact proof contracts;
registration points use the owned zero-commitment/default-point source bridge.
Native point/codec/group refinement and binding-signature opening knowledge
remain explicit. The conclusion is an alternative-representation event, not
unconditional conservation or universal independence of asset generators.
-/

structure Occurrence (B G : Type) where
  kind : Kind
  source : B
  commitment : G

def occurrences {B G : Type} (body : List (Occurrence B G))
    (fee : Option (Occurrence B G)) : List (Occurrence B G) := body ++ fee.toList

def registration {B G : Type} [Zero G] (source : B) : Occurrence B G :=
  ⟨.registerAsset, source, 0⟩

def sourceKey {B G : Type} [AddCommGroup G] (body : List (Occurrence B G))
    (fee : Option (Occurrence B G)) (feeGenerator : G) (feeAmount : Nat) : G :=
  groupSum ((occurrences body fee).map Occurrence.commitment) -
    (feeAmount : Int) • feeGenerator

theorem fee_occurrence_once {B G : Type} (body : List (Occurrence B G))
    (fee : Occurrence B G) : occurrences body (some fee) = body ++ [fee] := rfl

theorem occurrence_count {B G : Type} (body : List (Occurrence B G))
    (fee : Option (Occurrence B G)) (guard : body.length + fee.toList.length ≤ 512) :
    (occurrences body fee).length ≤ 512 := by
  simpa only [occurrences, List.length_append] using guard

theorem registration_zero {B G : Type} [Zero G] (source : B) :
    (registration source : Occurrence B G).source = source ∧
      (registration source : Occurrence B G).commitment = 0 := ⟨rfl, rfl⟩

theorem source_commitment_openings {B G : Type} [AddCommGroup G]
    (entries : List (Occurrence B G)) (extract : Occurrence B G → ActionOpening)
    (generators : Nat → G) (blindingGenerator : G)
    (each : ∀ entry ∈ entries, entry.commitment =
      (extract entry).value • generators (extract entry).asset +
        (extract entry).blinding • blindingGenerator) :
    groupSum (entries.map Occurrence.commitment) =
      nativeBalanceSum (nativeTerms generators (entries.map extract)) blindingGenerator := by
  unfold nativeBalanceSum nativeTerms
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro entry inside
  exact each entry inside

theorem native_key_decomposition {B G : Type} [AddCommGroup G]
    (body : List (Occurrence B G)) (fee : Option (Occurrence B G))
    (extract : Occurrence B G → ActionOpening) (generators : Nat → G)
    (blindingGenerator : G) (feeAsset feeAmount : Nat)
    (each : ∀ entry ∈ occurrences body fee, entry.commitment =
      (extract entry).value • generators (extract entry).asset +
        (extract entry).blinding • blindingGenerator) :
    sourceKey body fee (generators feeAsset) feeAmount =
      nativeBalanceSum (nativeTerms generators ((occurrences body fee).map extract)) blindingGenerator -
        (feeAmount : Int) • generators feeAsset := by
  unfold sourceKey
  rw [source_commitment_openings (occurrences body fee) extract generators blindingGenerator each]

theorem native_nonconservation_event
    {S : Type} [Field S] [CharP S ShielddSecurity.Scalar.order]
    {B G : Type} [AddCommGroup G]
    (body : List (Occurrence B G)) (fee : Option (Occurrence B G))
    (extract : Occurrence B G → ActionOpening) (generators : Nat → G)
    (blindingGenerator : G) (asset feeAsset feeAmount : Nat) (signatureOpening : Int)
    (guard : body.length + fee.toList.length ≤ 512)
    (bounded : ∀ entry ∈ occurrences body fee, (extract entry).value.natAbs < 2 ^ 129)
    (feeBound : feeAmount < 2 ^ 128)
    (each : ∀ entry ∈ occurrences body fee, entry.commitment =
      (extract entry).value • generators (extract entry).asset +
        (extract entry).blinding • blindingGenerator)
    (different : signedSum (selectedValues asset
      (semanticActions ((occurrences body fee).map extract))) ≠
        (selectedFee asset feeAsset feeAmount : Int))
    (extracted : sourceKey body fee (generators feeAsset) feeAmount =
      signatureOpening • blindingGenerator) :
    ∃ delta : Int,
      (aggregate (selectedValues asset (semanticActions ((occurrences body fee).map extract)))
        (selectedFee asset feeAsset feeAmount) : S) ≠ 0 ∧
      groupSum ((nativeTerms generators ((occurrences body fee).map extract)).map Prod.fst) -
        (feeAmount : Int) • generators feeAsset = delta • blindingGenerator := by
  have count : ((occurrences body fee).map extract).length ≤ 512 := by
    simpa only [List.length_map] using occurrence_count body fee guard
  have values : ∀ opening ∈ (occurrences body fee).map extract,
      opening.value.natAbs < 2 ^ 129 := by
    intro opening inside
    obtain ⟨entry, member, same⟩ := List.mem_map.mp inside
    subst opening
    exact bounded entry member
  have keySame := native_key_decomposition body fee extract generators blindingGenerator
    feeAsset feeAmount each
  have knowledge : nativeBalanceSum
      (nativeTerms generators ((occurrences body fee).map extract)) blindingGenerator -
        (feeAmount : Int) • generators feeAsset = signatureOpening • blindingGenerator :=
    keySame.symm.trans extracted
  exact nonconservation_exposes_representation_event (S := S) generators blindingGenerator
    ((occurrences body fee).map extract) asset feeAsset feeAmount signatureOpening
    count values feeBound different knowledge

set_option pp.all true in
#check @fee_occurrence_once
#print axioms fee_occurrence_once
set_option pp.all true in
#check @occurrence_count
#print axioms occurrence_count
set_option pp.all true in
#check @registration_zero
#print axioms registration_zero
set_option pp.all true in
#check @source_commitment_openings
#print axioms source_commitment_openings
set_option pp.all true in
#check @native_key_decomposition
#print axioms native_key_decomposition
set_option pp.all true in
#check @native_nonconservation_event
#print axioms native_nonconservation_event

end ShielddSecurity.TransferMixedCommitments
