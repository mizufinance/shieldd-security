import ShielddSecurity.TransferInstalledSourcePublication01
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option autoImplicit false
namespace ShielddSecurity.TransferInjectiveKeyPublication01
open TransferStateDelta
open TransferPendingFiniteCodec01 (NativePending restore)
open TransferBoundedNativeCodec01 (ExtendedObject encodeObject decodeObject nativeSupported nullifierModulus)
open TransferNullifierConsensusLimits01 (blockCapacity)
open TransferBlockPendingSequence01 (Request allInputs)
open TransferScalarLittleEndianBytes01 (scalarKey)
open TransferScalarMontgomeryValue01 (montgomeryValue)
open TransferSourceTypedInputProjection01 (typedWords installTypedInputs)
open TransferKnownFinalizerPublication01 (Effects installIo)
open TransferInstalledSourcePublication01 (SourceRequest installRequests)
/-! Pure injective natural labels for arbitrary finite Nat byte lists. This
is a symbolic key renaming, not hashing or a native cache implementation.
Empty/odd-head/even-successor coding derives global injection with finite
induction and small arithmetic lemmas. Installed whole source publication
uses the proved injection, with no caller key-injectivity premise. Native
String/byte/cache key identity and full trace/selector/codec/ownership/OS
correspondence remain explicit; no native/control/certification credit. -/

def consCode : Nat → Nat → Nat
  | 0, tail => 2 * tail + 1
  | head + 1, tail => 2 * (consCode head tail + 1)

def keyCode : Bytes → Nat
  | [] => 0
  | head :: tail => consCode head (keyCode tail)

theorem consCode_is_positive (head tail : Nat) : 0 < consCode head tail := by
  cases head <;> simp only [consCode] <;> omega

theorem consCode_derives_exact_head_and_tail (a b x y : Nat) (same : consCode a x = consCode b y) :
    a = b ∧ x = y := by
  induction a generalizing b x y with
  | zero =>
    cases b with
    | zero =>
      change 2 * x + 1 = 2 * y + 1 at same
      exact ⟨rfl, by omega⟩
    | succ b =>
      change 2 * x + 1 = 2 * (consCode b y + 1) at same
      omega
  | succ a ih =>
    cases b with
    | zero =>
      change 2 * (consCode a x + 1) = 2 * y + 1 at same
      omega
    | succ b =>
      have inner : consCode a x = consCode b y := by
        change 2 * (consCode a x + 1) = 2 * (consCode b y + 1) at same
        omega
      obtain ⟨heads, tails⟩ := ih b x y inner
      exact ⟨congrArg Nat.succ heads, tails⟩

theorem keyCode_is_injective : Function.Injective keyCode := by
  intro left
  induction left with
  | nil =>
    intro right same
    cases right with
    | nil => rfl
    | cons head tail =>
      have positive := consCode_is_positive head (keyCode tail)
      change 0 = consCode head (keyCode tail) at same
      omega
  | cons head tail ih =>
    intro right same
    cases right with
    | nil =>
      have positive := consCode_is_positive head (keyCode tail)
      change consCode head (keyCode tail) = 0 at same
      omega
    | cons other rest =>
      have pair := consCode_derives_exact_head_and_tail head other (keyCode tail) (keyCode rest) same
      exact congrArg₂ List.cons pair.1 (@ih rest pair.2)

theorem injective_labeled_source_and_finalizer_publish_exact_global_mathematical_input_vector {O E K X Tree A I : Type}
    (encodeNative : NativePending → O) (decodeNative : O → NativePending)
    (supportedRoundtrip : ∀ native, nativeSupported native = true → restore (decodeNative (encodeNative native)) = restore native)
    (inputs : A → List I) (wordOf : I → Vector UInt64 4)
    (sourceRequests : List (SourceRequest (ExtendedObject O) E K X Tree A I inputs))
    (parent : State (ExtendedObject O)) (queued : List A) (final : State (ExtendedObject O) × List A)
    (storedNativeDefault : parent.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) =
      some (.inl (encodeNative (.opened [] []))))
    (walkedNative : TransferBlockPendingSequence01.walk (TransferNativeReachableErasure01.nativeOnlyEncode encodeNative)
      (TransferPendingFiniteCodec01.decode (decodeObject decodeNative)) keyCode parent queued (installRequests inputs wordOf sourceRequests) = some final)
    (effectsOf : Fin (2 ^ 64) → State (ExtendedObject O) → List A → Effects (ExtendedObject O) E A)
    (baseIo : TransferEndToEnd01.Io (ExtendedObject O) E A) (host : TransferHostSealedCommit01.Host (ExtendedObject O))
    (height : Fin (2 ^ 64)) (root : Nat) (currentState : host.active = final.1)
    (typedGetter : (installIo encodeNative decodeNative keyCode effectsOf baseIo).ending.decodePending (.inl (encodeNative (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) = restore (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))
    (success : (TransferEndToEnd01.execute (installIo encodeNative decodeNative keyCode effectsOf baseIo) host height final.2).root = some root) :
    allInputs (installRequests inputs wordOf sourceRequests) = (sourceRequests.flatMap (fun request => typedWords inputs wordOf request.base.action)).map montgomeryValue ∧
    ∃ state,
      (TransferHostEndBlock01.transferred (installIo encodeNative decodeNative keyCode effectsOf baseIo).ending host height final.2).returned = some state ∧
      state.objects (keyCode TransferNullifierObjectKeys01.nullifierBytes) = some (.inl (encodeNative (.sealed (allInputs (installRequests inputs wordOf sourceRequests))))) ∧
      (allInputs (installRequests inputs wordOf sourceRequests)).Nodup ∧ (allInputs (installRequests inputs wordOf sourceRequests)).length ≤ blockCapacity ∧
      (∀ key ∈ allInputs (installRequests inputs wordOf sourceRequests), key < nullifierModulus) ∧
      ∃ (frozen : TransferWriterPrepareSource01.Frozen), frozen.insertions.accepted = allInputs (installRequests inputs wordOf sourceRequests) ∧ frozen.next.applicationRoot = some root ∧
        (TransferEndToEnd01.execute (installIo encodeNative decodeNative keyCode effectsOf baseIo) host height final.2).host.writer = .ready frozen.next ∧
        (TransferEndToEnd01.execute (installIo encodeNative decodeNative keyCode effectsOf baseIo) host height final.2).host.phase = .idle ∧
        (TransferEndToEnd01.execute (installIo encodeNative decodeNative keyCode effectsOf baseIo) host height final.2).host.store.actualRoots = frozen.next.nullifiers.roots ∧
        (TransferEndToEnd01.execute (installIo encodeNative decodeNative keyCode effectsOf baseIo) host height final.2).host.store.boundary = some frozen.next.nullifiers := by
  exact TransferInstalledSourcePublication01.installed_source_and_finalizer_publish_exact_global_mathematical_input_vector
    encodeNative decodeNative supportedRoundtrip keyCode keyCode_is_injective inputs wordOf sourceRequests parent queued final storedNativeDefault
    walkedNative effectsOf baseIo host height root currentState typedGetter success
set_option pp.all true in
#check @consCode
#print axioms consCode
set_option pp.all true in
#check @keyCode
#print axioms keyCode
set_option pp.all true in
#check @consCode_is_positive
#print axioms consCode_is_positive
set_option pp.all true in
#check @consCode_derives_exact_head_and_tail
#print axioms consCode_derives_exact_head_and_tail
set_option pp.all true in
#check @keyCode_is_injective
#print axioms keyCode_is_injective
set_option pp.all true in
#check @injective_labeled_source_and_finalizer_publish_exact_global_mathematical_input_vector
#print axioms injective_labeled_source_and_finalizer_publish_exact_global_mathematical_input_vector
end ShielddSecurity.TransferInjectiveKeyPublication01
