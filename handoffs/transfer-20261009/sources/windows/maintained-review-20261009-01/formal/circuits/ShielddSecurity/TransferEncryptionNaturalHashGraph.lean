import ShielddSecurity.TransferEncryptionNativeHashGraph
import ShielddSecurity.RuntimeTransferEncryptionFieldCipherGraph

set_option maxHeartbeats 400000

namespace ShielddSecurity.TransferEncryptionNaturalHashGraph

variable {F : Type} [Field F] [CharP F Scalar.modulus]
variable (codec : TransferReduction.CanonicalField F)

def naturalInputs (rho : Nat → F) (call : Nat) : List Nat :=
  (RuntimeTransferEncryptionHashGraph.inputs call).map (fun input => codec.decode (eval rho input))

/-- One interpretation for every input list and domain, using the actual small
and wide recipes and the arity-dependent IV. Native source/caller bindings and
the complete Transfer crypto interpretation remain separate obligations. -/
def naturalHash (domain : Nat) (inputs : List Nat) : Nat :=
  codec.decode (Poseidon.hash
    (Poseidon.castParameters RuntimeTransferEncryptionHashGroup0.smallRecipe)
    (Poseidon.castParameters RuntimeTransferEncryptionHashGroup0.wideRecipe)
    domain (inputs.map (fun value : Nat => (value : F))))

theorem inputs_roundtrip (rho : Nat → F) (call : Nat) :
    (naturalInputs codec rho call).map (fun value : Nat => (value : F)) =
      (RuntimeTransferEncryptionHashGraph.inputs call).map (eval rho) := by
  simp only [naturalInputs, List.map_map, Function.comp_def, codec.roundtrip]

/-- All twenty-four captured calls decode to the same canonical natural hash
interpretation, from the actual row satisfaction at the same assignment. -/
theorem all_hashes_natural (rho : Nat → F) (one : rho 0 = 1)
    (satisfied : Satisfies rho RuntimeTransferEncryptionHashGraph.rawRows) (call : Fin 24) :
    codec.decode (eval rho (RuntimeTransferEncryptionHashGraph.output call.val)) =
      naturalHash codec (TransferEncryptionNativeHashGraph.domain call.val)
        (naturalInputs codec rho call.val) := by
  have rows := RuntimeTransferEncryptionHashGraph.all_hashes_sound rho one satisfied call
  have recipe := TransferEncryptionNativeHashGraph.recipe call
    ((RuntimeTransferEncryptionHashGraph.inputs call.val).map (eval rho))
    (by simpa only [List.length_map] using TransferEncryptionNativeHashGraph.inputs_length call)
  rw [recipe] at rows
  simpa only [naturalHash, inputs_roundtrip] using congrArg codec.decode rows

/-- The computed field hash values in the ciphertext joins use exactly that
interpretation. This lemma makes no claim that a row is satisfied. -/
theorem hash_value_natural (rho : Nat → F) (call : Fin 24) :
    codec.decode (RuntimeTransferEncryptionFieldCipherGraph.hashValue rho call.val) =
      naturalHash codec (TransferEncryptionNativeHashGraph.domain call.val)
        (naturalInputs codec rho call.val) := by
  have recipe := TransferEncryptionNativeHashGraph.recipe call
    ((RuntimeTransferEncryptionHashGraph.inputs call.val).map (eval rho))
    (by simpa only [List.length_map] using TransferEncryptionNativeHashGraph.inputs_length call)
  simpa only [RuntimeTransferEncryptionFieldCipherGraph.hashValue, naturalHash, inputs_roundtrip]
    using congrArg codec.decode recipe

set_option pp.all true in
#check @inputs_roundtrip
#print axioms inputs_roundtrip
set_option pp.all true in
#check @all_hashes_natural
#print axioms all_hashes_natural
set_option pp.all true in
#check @hash_value_natural
#print axioms hash_value_natural

end ShielddSecurity.TransferEncryptionNaturalHashGraph
