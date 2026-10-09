import ShielddSecurity.TransferNativeFieldBridge

set_option maxHeartbeats 200000

namespace ShielddSecurity.TransferNativeStatementSequence

/-! The nested source shape and append order of transfer::Statement::fields.
The constructor retains every tier, slot and policy field independently.
Instantiation with the actual decoded Rust objects remains a source-refinement
obligation; codec contracts remain those of TransferNativeFieldBridge. -/

structure Point (F : Type) where
  x : F
  y : F

structure Output (F : Type) where
  note : F
  recovery : F

structure Core (F : Type) where
  epk : Point F
  c2 : F
  ciphertext : F
  confirmation : F

structure Extended (F : Type) where
  epk : Point F
  c2 : F
  ciphertext : F × F × F

structure Policy (F : Type) where
  ringId : F
  policyId : F
  resource : F
  permission : F

structure Volume (F : Type) where
  nullifier : F
  commitment : F
  dayStart : F
  context : F

structure Ownership (F : Type) where
  r : Point F
  c : Point F

structure Audit (F : Type) where
  detection : F × F × F × F
  senderCore : Core F
  senderExt : Extended F
  outputCore : Core F
  outputExt : Extended F
  policy : Policy F
  salts : F × F × F × F
  auditEpoch : F
  ownership : Ownership F × Ownership F

structure Source (F : Type) where
  rk : Point F
  anchor : F
  outputs : Output F × Output F
  balance : Point F
  routingTags : F × F
  routingParameter : F
  volume : Volume F
  spends : F × F
  assetAnchor : F
  complianceAnchor : F
  audit : Audit F
  timestamp : F

def pointFields {F : Type} (p : Point F) : List F := [p.x, p.y]
def outputFields {F : Type} (o : Output F) : List F := [o.note, o.recovery]
def coreFields {F : Type} (c : Core F) : List F :=
  pointFields c.epk ++ [c.c2, c.ciphertext]
def extendedFields {F : Type} (e : Extended F) : List F :=
  pointFields e.epk ++ [e.c2] ++ [e.ciphertext.1, e.ciphertext.2.1, e.ciphertext.2.2]
def ownershipFields {F : Type} (o : Ownership F) : List F := pointFields o.r ++ pointFields o.c

def rustFields {F : Type} (s : Source F) : List F :=
  pointFields s.rk ++ [s.anchor] ++
  outputFields s.outputs.1 ++ outputFields s.outputs.2 ++ pointFields s.balance ++
  [s.routingTags.1, s.routingTags.2] ++
  [s.routingParameter, s.volume.nullifier, s.volume.commitment, s.volume.dayStart, s.volume.context] ++
  [s.spends.1, s.spends.2] ++ [s.assetAnchor, s.complianceAnchor] ++
  [s.audit.detection.1, s.audit.detection.2.1, s.audit.detection.2.2.1, s.audit.detection.2.2.2] ++
  coreFields s.audit.senderCore ++ extendedFields s.audit.senderExt ++
  coreFields s.audit.outputCore ++ extendedFields s.audit.outputExt ++
  [s.timestamp, s.audit.senderCore.confirmation, s.audit.outputCore.confirmation,
   s.audit.policy.ringId, s.audit.policy.policyId, s.audit.policy.resource, s.audit.policy.permission] ++
  [s.audit.salts.1, s.audit.salts.2.1, s.audit.salts.2.2.1, s.audit.salts.2.2.2] ++
  [s.audit.auditEpoch] ++ ownershipFields s.audit.ownership.1 ++ ownershipFields s.audit.ownership.2

def semantic {F : Type} (s : Source F) : TransferStatement F :=
  { rkX := s.rk.x
    rkY := s.rk.y
    anchor := s.anchor
    recipientNote := s.outputs.1.note
    recipientRecovery := s.outputs.1.recovery
    changeNote := s.outputs.2.note
    changeRecovery := s.outputs.2.recovery
    balanceX := s.balance.x
    balanceY := s.balance.y
    routingSlot0 := s.routingTags.1
    routingSlot1 := s.routingTags.2
    routingParameters := s.routingParameter
    volumeNullifier := s.volume.nullifier
    volumeCommitment := s.volume.commitment
    volumeDayStart := s.volume.dayStart
    volumeContext := s.volume.context
    firstNullifier := s.spends.1
    secondNullifier := s.spends.2
    assetRoot := s.assetAnchor
    userRoot := s.complianceAnchor
    detection0 := s.audit.detection.1
    detection1 := s.audit.detection.2.1
    detection2 := s.audit.detection.2.2.1
    detection3 := s.audit.detection.2.2.2
    senderCoreEpkX := s.audit.senderCore.epk.x
    senderCoreEpkY := s.audit.senderCore.epk.y
    senderCoreC2 := s.audit.senderCore.c2
    senderCoreCiphertext := s.audit.senderCore.ciphertext
    senderExtEpkX := s.audit.senderExt.epk.x
    senderExtEpkY := s.audit.senderExt.epk.y
    senderExtC2 := s.audit.senderExt.c2
    senderExtCiphertext0 := s.audit.senderExt.ciphertext.1
    senderExtCiphertext1 := s.audit.senderExt.ciphertext.2.1
    senderExtCiphertext2 := s.audit.senderExt.ciphertext.2.2
    outputCoreEpkX := s.audit.outputCore.epk.x
    outputCoreEpkY := s.audit.outputCore.epk.y
    outputCoreC2 := s.audit.outputCore.c2
    outputCoreCiphertext := s.audit.outputCore.ciphertext
    outputExtEpkX := s.audit.outputExt.epk.x
    outputExtEpkY := s.audit.outputExt.epk.y
    outputExtC2 := s.audit.outputExt.c2
    outputExtCiphertext0 := s.audit.outputExt.ciphertext.1
    outputExtCiphertext1 := s.audit.outputExt.ciphertext.2.1
    outputExtCiphertext2 := s.audit.outputExt.ciphertext.2.2
    timestamp := s.timestamp
    senderCoreConfirmation := s.audit.senderCore.confirmation
    outputCoreConfirmation := s.audit.outputCore.confirmation
    ringId := s.audit.policy.ringId
    policyId := s.audit.policy.policyId
    resource := s.audit.policy.resource
    permission := s.audit.policy.permission
    senderCoreSalt := s.audit.salts.1
    senderExtSalt := s.audit.salts.2.1
    outputCoreSalt := s.audit.salts.2.2.1
    outputExtSalt := s.audit.salts.2.2.2
    auditEpoch := s.audit.auditEpoch
    senderOwnershipRX := s.audit.ownership.1.r.x
    senderOwnershipRY := s.audit.ownership.1.r.y
    senderOwnershipCX := s.audit.ownership.1.c.x
    senderOwnershipCY := s.audit.ownership.1.c.y
    recipientOwnershipRX := s.audit.ownership.2.r.x
    recipientOwnershipRY := s.audit.ownership.2.r.y
    recipientOwnershipCX := s.audit.ownership.2.c.x
    recipientOwnershipCY := s.audit.ownership.2.c.y }

theorem source_sequence_exact {F : Type} (s : Source F) :
    rustFields s = (semantic s).fields := by
  simp only [rustFields, pointFields, outputFields, coreFields, extendedFields,
    ownershipFields, TransferStatement.fields, semantic, List.cons_append, List.nil_append]

private theorem point_length {F : Type} (p : Point F) : (pointFields p).length = 2 := rfl
private theorem output_length {F : Type} (o : Output F) : (outputFields o).length = 2 := rfl
private theorem core_length {F : Type} (c : Core F) : (coreFields c).length = 4 := by
  simp only [coreFields, List.length_append, point_length, List.length_cons, List.length_nil]
private theorem extended_length {F : Type} (e : Extended F) : (extendedFields e).length = 6 := by
  simp only [extendedFields, List.length_append, point_length, List.length_cons, List.length_nil]
private theorem ownership_length {F : Type} (o : Ownership F) : (ownershipFields o).length = 4 := by
  simp only [ownershipFields, List.length_append, point_length]

theorem source_sequence_length {F : Type} (s : Source F) :
    (rustFields s).length = 64 := by
  simp only [rustFields, List.length_append, point_length, output_length, core_length,
    extended_length, ownership_length, List.length_cons, List.length_nil]

/-- An equality of sequences determines all source-view semantic fields;
no hash-injectivity premise or key/message interpretation is used. -/
theorem source_sequence_injective {F : Type} (s t : Source F)
    (same : rustFields s = rustFields t) : semantic s = semantic t := by
  rw [source_sequence_exact, source_sequence_exact] at same
  exact TransferStatement.fields_injective same

variable {F Sdk Raw Encoded : Type} [Field F] [CharP F Scalar.modulus]

theorem source_sequence_conversion
    (operations : ShielddNativeScalar.Operations (F := F) Raw)
    (primitives : ShielddNativeScalar.ReadPrimitives Encoded Raw operations)
    (sdk : TransferNativeFieldBridge.SdkEncoder Sdk F) (s : Source Sdk) :
    ∃ outputs, TransferNativeFieldBridge.fields operations primitives sdk (rustFields s) = some outputs ∧
      outputs.map (ShielddNativeScalar.value operations) = (rustFields s).map sdk.value ∧
      outputs.length = 64 := by
  obtain ⟨outputs, read, meaning, count⟩ :=
    TransferNativeFieldBridge.fields_success operations primitives sdk (rustFields s)
  exact ⟨outputs, read, meaning, count.trans (source_sequence_length s)⟩

set_option pp.all true in
#check @source_sequence_exact
#print axioms source_sequence_exact

set_option pp.all true in
#check @source_sequence_length
#print axioms source_sequence_length

set_option pp.all true in
#check @source_sequence_injective
#print axioms source_sequence_injective

set_option pp.all true in
#check @source_sequence_conversion
#print axioms source_sequence_conversion

end ShielddSecurity.TransferNativeStatementSequence
