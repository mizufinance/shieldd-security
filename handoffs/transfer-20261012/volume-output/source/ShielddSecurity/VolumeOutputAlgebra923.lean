import ShielddSecurity.VolumeOutputCapture922
import ShielddSecurity.TransferSem
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeOutputAlgebra923
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 TransferSem
variable {F : Type} [Field F] [CharP F p]
attribute [local irreducible] SatisfiesAt
structure Values (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness) : Prop where
  copied : rho copy=1
  context : rho 7607=(w.volume.context:F)
  useReal : rho 7605=(if w.volume.useReal then 1 else 0)
  newDay : rho 7606=(if w.volume.startsNewDay then 1 else 0)
  nullifier : rho 8509=(w.volume.nullifier:F)
  commitment : rho 8510=(w.volume.commitment:F)
  origin : eval rho VolumeOutputHash918C149.result=(c.hash .volumeOriginNullifier [w.auth.nk,w.volume.subject,w.volume.dayStart]:F)
  previous : eval rho VolumeOutputHash918C150.result=(c.hash .noteNullifier [w.auth.nk,volumeState c w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding,w.volume.priorPosition]:F)
  state : eval rho VolumeOutputHash918C151.result=(volumeState c w.volume.subject w.volume.dayStart w.volume.successor w.volume.successorBlinding:F)
  paddingNullifier : eval rho VolumeOutputHash918C152.result=(c.hash .volumePaddingNullifier [w.auth.nk,w.nonce,w.volume.dayStart]:F)
  paddingCommitment : eval rho VolumeOutputHash918C153.result=(c.hash .volumePaddingCommitment [w.auth.nk,w.nonce,w.volume.dayStart]:F)

theorem rows (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (volume : VolumeSem c w) (values : Values rho c w)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) : VolumeOutputCapture922.Rows rho := by
  obtain ⟨_,_,_,_,context,_,_,_,_,_,_,_,_,nullifier,commitment⟩ := volume
  apply VolumeOutputCapture922.rows
  · rw [VolumeOutputCapture922.nullifier_value rho arithmetic,VolumeOutputCapture922.nullifierSelect_value rho arithmetic,
      VolumeOutputCapture922.originSelect_value rho arithmetic,values.copied,values.context,values.useReal,values.newDay,
      values.nullifier,values.origin,values.previous,values.paddingNullifier,nullifier]
    rcases context with context|context <;> cases real : w.volume.useReal <;> cases day : w.volume.startsNewDay <;>
      norm_num [context,real,day,volumeState] <;> ring
  · rw [VolumeOutputCapture922.commitment_value rho arithmetic,VolumeOutputCapture922.commitmentSelect_value rho arithmetic,
      values.copied,values.context,values.useReal,values.commitment,values.state,values.paddingCommitment,commitment]
    rcases context with context|context <;> cases real : w.volume.useReal <;>
      norm_num [context,real,volumeState] <;> ring
end ShielddSecurity.VolumeOutputAlgebra923

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputAlgebra923.Values
#print axioms ShielddSecurity.VolumeOutputAlgebra923.Values

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputAlgebra923.rows
#print axioms ShielddSecurity.VolumeOutputAlgebra923.rows
