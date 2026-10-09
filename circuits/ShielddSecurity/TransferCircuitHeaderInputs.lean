import ShielddSecurity.TransferCircuitInputSeed

set_option maxHeartbeats 150000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferCircuitHeaderInputs
open TransferSem

/-! The first eight witness inputs allocated by the pinned Transfer constrain
function, in allocation order. These are source input indices, not compiler
columns: the compiler's reserved public and committed columns are distinct.
Remaining gadget inputs are still supplied by their owned construction.
This header codec alone does not construct all 22,735 circuit inputs or bind a
complete source graph to Rust. -/

def values {F : Type} [Field F] (w : TransferSem.Witness)
    (remaining : Nat → F) : Nat → F
  | 0 => (w.anchor : F)
  | 1 => (w.assetAnchor : F)
  | 2 => (w.userAnchor : F)
  | 3 => (w.asset : F)
  | 4 => (w.timestamp : F)
  | 5 => (w.nonce : F)
  | 6 => (w.blinding : F)
  | 7 => if w.regulated then 1 else 0
  | index => remaining index

theorem header_order {F : Type} [Field F] (w : TransferSem.Witness)
    (remaining : Nat → F) :
    values w remaining 0 = (w.anchor : F) ∧
      values w remaining 1 = (w.assetAnchor : F) ∧
      values w remaining 2 = (w.userAnchor : F) ∧
      values w remaining 3 = (w.asset : F) ∧
      values w remaining 4 = (w.timestamp : F) ∧
      values w remaining 5 = (w.nonce : F) ∧
      values w remaining 6 = (w.blinding : F) ∧
      values w remaining 7 = (if w.regulated then 1 else 0) := by
  simp [values]

theorem remaining_inputs_preserved {F : Type} [Field F] (w : TransferSem.Witness)
    (remaining : Nat → F) (offset : Nat) :
    values w remaining (offset + 8) = remaining (offset + 8) := by
  rfl

theorem regulated_assertion {F : Type} [Field F] (w : TransferSem.Witness)
    (remaining : Nat → F) :
    Square (values w remaining 7) (values w remaining 7) := by
  cases selected : w.regulated <;> simp [values, Square, selected]

theorem constructed_regulated_assertion {F : Type} [Field F] (c : Crypto)
    (i : TransferSemanticConstruction.Inputs c) (remaining : Nat → F) :
    Square (values (TransferSemanticConstruction.construct c i) remaining 7)
      (values (TransferSemanticConstruction.construct c i) remaining 7) :=
  regulated_assertion (TransferSemanticConstruction.construct c i) remaining

theorem recovered_header_preserved {F : Type} [Field F] (c : Crypto)
    (w : TransferSem.Witness) (zeroMul : TransferEncryptionDecomposition.MulZeroLaw c)
    (legal : TransferSem.TransferSem c w) (remaining : Nat → F) :
    values (TransferSemanticConstruction.construct c
      (TransferSemanticInputRecovery.recover c w zeroMul legal)) remaining =
      values w remaining := by
  rw [TransferSemanticInputRecovery.constructed_stage_agrees,
    TransferTailEncryptionRecovery.normalized_record]
  rfl

set_option pp.all true in
#check @header_order
#print axioms header_order
set_option pp.all true in
#check @remaining_inputs_preserved
#print axioms remaining_inputs_preserved
set_option pp.all true in
#check @regulated_assertion
#print axioms regulated_assertion
set_option pp.all true in
#check @constructed_regulated_assertion
#print axioms constructed_regulated_assertion
set_option pp.all true in
#check @recovered_header_preserved
#print axioms recovered_header_preserved

end ShielddSecurity.TransferCircuitHeaderInputs
