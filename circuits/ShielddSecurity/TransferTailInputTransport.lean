import ShielddSecurity.TransferVolumeBranchCompletion
import ShielddSecurity.TransferEncryptionBranchCompletion
import ShielddSecurity.TransferRoutingBranchCompletion

set_option maxHeartbeats 300000
set_option maxRecDepth 4096

namespace ShielddSecurity.TransferTailInputTransport
open TransferCore TransferSem

/-! The frame lists ordinary input fields read by the tail constructors.
Unfinished volume, encryption and routing storage is excluded. -/
structure Frame (base old : TransferSem.Witness) : Prop where
  anchor : base.anchor = old.anchor
  asset : base.asset = old.asset
  regulated : base.regulated = old.regulated
  registry : base.registry = old.registry
  sender : base.sender = old.sender
  receiver : base.receiver = old.receiver
  outputs : base.outputs = old.outputs
  authorization : base.auth = old.auth
  timestamp : base.timestamp = old.timestamp
  nonce : base.nonce = old.nonce

def transportVolume (c : Crypto) (base old : TransferSem.Witness) (frame : Frame base old)
    (i : TransferVolumeBranchCompletion.LegalVolumeInputs c old) :
    TransferVolumeBranchCompletion.LegalVolumeInputs c base where
  toInputs := i.toInputs
  timestampBound := by simpa only [frame.timestamp] using i.timestampBound
  dayBound := i.dayBound
  secondBound := i.secondBound
  timeSplit := by simpa only [frame.timestamp] using i.timeSplit
  contextValid := i.contextValid
  feeSelf := by simpa only [external, frame.sender, frame.receiver] using i.feeSelf
  trackedEligible := by simpa only [frame.regulated, external, frame.sender, frame.receiver] using i.trackedEligible
  priorBound := i.priorBound
  outboundPositive := by simpa only [frame.outputs] using i.outboundPositive
  outboundBound := by simpa only [frame.outputs] using i.outboundBound
  candidateBound := by simpa only [frame.outputs] using i.candidateBound
  limitBound := by simpa only [frame.registry] using i.limitBound
  positionBound := i.positionBound
  trackedLimit := by simpa only [frame.outputs, frame.registry] using i.trackedLimit
  originZero := i.originZero
  continuationAuthenticated := by
    simpa only [TransferVolumeBranchCompletion.selectedSubject, frame.sender, frame.asset, frame.anchor]
      using i.continuationAuthenticated

theorem volume_raw_preserved (c : Crypto) (base old : TransferSem.Witness) (frame : Frame base old)
    (i : TransferVolumeBranchCompletion.LegalVolumeInputs c old) :
    (transportVolume c base old frame i).toInputs = i.toInputs := rfl

theorem volume_construct_agrees (c : Crypto) (base old : TransferSem.Witness) (frame : Frame base old)
    (i : TransferVolumeBranchCompletion.LegalVolumeInputs c old) :
    TransferVolumeBranchCompletion.construct c base (transportVolume c base old frame i) =
      TransferVolumeBranchCompletion.construct c old i := by
  simp only [TransferVolumeBranchCompletion.construct, transportVolume,
    TransferVolumeBranchCompletion.selectedSubject, TransferVolumeBranchCompletion.predecessor,
    frame.sender, frame.asset, frame.outputs, frame.authorization, frame.nonce]

structure EncryptionFrame (base old : TransferSem.Witness) : Prop extends Frame base old where
  volumeContext : base.volume.context = old.volume.context
  volumeUseReal : base.volume.useReal = old.volume.useReal

def transportEncryption (c : Crypto) (base old : TransferSem.Witness) (frame : EncryptionFrame base old)
    (i : TransferEncryptionBranchCompletion.LegalEncryptionInputs c old) :
    TransferEncryptionBranchCompletion.LegalEncryptionInputs c base where
  seeds := i.seeds
  ephemeral := i.ephemeral
  ownershipRandomness := i.ownershipRandomness
  seedCanonical := i.seedCanonical
  ephemeralBounded := i.ephemeralBounded
  ephemeralNonzero := i.ephemeralNonzero
  ownershipBounded := i.ownershipBounded
  ownershipNonzero := i.ownershipNonzero
  epkNonidentity := i.epkNonidentity
  ownershipNonidentity := i.ownershipNonidentity
  detectionNonidentity := by simpa only [detectionKey, frame.regulated, frame.registry] using i.detectionNonidentity
  checkingNonidentity := by simpa only [checkingKey, frame.regulated, frame.registry] using i.checkingNonidentity

theorem encryption_raw_preserved (c : Crypto) (base old : TransferSem.Witness) (frame : EncryptionFrame base old)
    (i : TransferEncryptionBranchCompletion.LegalEncryptionInputs c old) :
    (transportEncryption c base old frame i).seeds = i.seeds ∧
      (transportEncryption c base old frame i).ephemeral = i.ephemeral ∧
      (transportEncryption c base old frame i).ownershipRandomness = i.ownershipRandomness :=
  ⟨rfl, rfl, rfl⟩

theorem encryption_construct_agrees (c : Crypto) (base old : TransferSem.Witness)
    (frame : EncryptionFrame base old) (i : TransferEncryptionBranchCompletion.LegalEncryptionInputs c old) :
    TransferEncryptionBranchCompletion.construct c base (transportEncryption c base old frame i) =
      TransferEncryptionBranchCompletion.construct c old i := by
  have tiers : TransferEncryptionBranchCompletion.constructTier c base (transportEncryption c base old frame i) =
      TransferEncryptionBranchCompletion.constructTier c old i := by
    funext slot
    simp only [TransferEncryptionBranchCompletion.constructTier, transportEncryption,
      TransferEncryptionBranchCompletion.selectedKey, flagged, TransferSem.eligible, external,
      detectionKey, payloadKey, salt, frame.regulated, frame.registry, frame.sender, frame.receiver,
      frame.outputs, frame.nonce, frame.volumeContext, frame.volumeUseReal]
  have ownership : TransferEncryptionBranchCompletion.constructOwnership c base (transportEncryption c base old frame i) =
      TransferEncryptionBranchCompletion.constructOwnership c old i := by
    funext slot
    simp only [TransferEncryptionBranchCompletion.constructOwnership, transportEncryption,
      checkingKey, frame.regulated, frame.registry, frame.sender, frame.receiver]
  unfold TransferEncryptionBranchCompletion.construct
  rw [tiers, ownership]
  simp only [transportEncryption, TransferEncryptionBranchCompletion.detectionSeed,
    flagged, TransferSem.eligible, external, detectionKey, salt,
    frame.asset, frame.regulated, frame.registry, frame.sender, frame.receiver, frame.outputs,
    frame.timestamp, frame.nonce, frame.volumeContext, frame.volumeUseReal]
  rfl

theorem routing_construct_agrees (c : Crypto) (base old : TransferSem.Witness) (frame : Frame base old)
    (i : TransferRoutingBranchCompletion.LegalRoutingInputs) :
    TransferRoutingBranchCompletion.construct c base i = TransferRoutingBranchCompletion.construct c old i := by
  simp only [TransferRoutingBranchCompletion.construct, TransferRoutingBranchCompletion.bits,
    TransferRoutingBranchCompletion.selectedWord, TransferRoutingBranchCompletion.meaningful,
    TransferRoutingBranchCompletion.senderSlot, TransferRoutingBranchCompletion.swapped,
    TransferRoutingBranchCompletion.routeWord, TransferRoutingBranchCompletion.randomWord,
    TransferRoutingBranchCompletion.precision, frame.sender, frame.receiver, frame.outputs,
    frame.regulated, frame.nonce]
  rfl

set_option pp.all true in
#check @volume_raw_preserved
#print axioms volume_raw_preserved
set_option pp.all true in
#check @volume_construct_agrees
#print axioms volume_construct_agrees
set_option pp.all true in
#check @encryption_raw_preserved
#print axioms encryption_raw_preserved
set_option pp.all true in
#check @encryption_construct_agrees
#print axioms encryption_construct_agrees
set_option pp.all true in
#check @routing_construct_agrees
#print axioms routing_construct_agrees

end ShielddSecurity.TransferTailInputTransport
