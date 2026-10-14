import ShielddSecurity.VolumeOutputValues920
import ShielddSecurity.VolumeOutputHashes919
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.VolumeOutputMeaning921
open Compiler CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open VolumeHashAssignment892 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model SatisfiesAt PoseidonNatural192.hash Poseidon.hash6 TransferSem.volumeState
theorem natural149 (c : Crypto) (w : TransferSem.Witness) :
    ((BalanceBlindingDomain670.crypto c).hash .volumeOriginNullifier [(w.auth.nk),(w.volume.subject),(w.volume.dayStart)]:F)=Poseidon.hash6 (Poseidon.castParameters VolumeOutputHash918C149.parameters) 6 [(w.auth.nk:F),(w.volume.subject:F),(w.volume.dayStart:F)] := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide ConcreteRegistrySharedEncoding294.representation
    .volumeOriginNullifier [(w.auth.nk),(w.volume.subject),(w.volume.dayStart)]:F)=_
  rw [show Poseidon.castParameters VolumeOutputHash918C149.parameters=(RegistryNatural193.wide : Poseidon.Parameters F 6) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_neg (by change ¬3≤2;decide)]
  rfl
theorem ports149 (rho : Nat → F) : VolumeOutputHash918C149.inputs.map (eval rho)=[rho 1993,rho 7740,rho 7739] := by
  simp [VolumeOutputHash918C149.inputs,eval]
theorem hash149 (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumeOutputHash918C149.result=((BalanceBlindingDomain670.crypto c).hash .volumeOriginNullifier [(w.auth.nk),(w.volume.subject),(w.volume.dayStart)]:F) := by
  have zero : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 := by
    unfold assignment
    exact RoutingParameterValues879.zero _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial CapturedInitial73419Generic01.copy=1 := by
    unfold assignment
    exact RoutingParameterValues879.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic : SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
    unfold assignment
    exact RoutingParameterValues879.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have result := VolumeOutputHash918C149.hash _ zero (copied.trans zero.symm) arithmetic
  rw [ports149,VolumeOutputValues920.key original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumeHashAssignment892.subject original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumePriorValues909.day_start original u c w legal rkInitial authInitial initial senderInitial receiverInitial] at result
  exact result.trans (natural149 c w).symm
theorem natural150 (c : Crypto) (w : TransferSem.Witness) :
    ((BalanceBlindingDomain670.crypto c).hash .noteNullifier [(w.auth.nk),(volumeState (BalanceBlindingDomain670.crypto c) w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding),(w.volume.priorPosition)]:F)=Poseidon.hash6 (Poseidon.castParameters VolumeOutputHash918C150.parameters) 7 [(w.auth.nk:F),(volumeState (BalanceBlindingDomain670.crypto c) w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding:F),(w.volume.priorPosition:F)] := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide ConcreteRegistrySharedEncoding294.representation
    .noteNullifier [(w.auth.nk),(volumeState (BalanceBlindingDomain670.crypto c) w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding),(w.volume.priorPosition)]:F)=_
  rw [show Poseidon.castParameters VolumeOutputHash918C150.parameters=(RegistryNatural193.wide : Poseidon.Parameters F 6) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_neg (by change ¬3≤2;decide)]
  rfl
theorem ports150 (rho : Nat → F) : VolumeOutputHash918C150.inputs.map (eval rho)=[rho 1993,eval rho VolumePriorHash908.result,rho 8387] := by
  have shape : VolumeOutputHash918C150.inputs=[[(1993,1)],VolumePriorHash908.result,[(8387,1)]] := by decide +kernel
  rw [shape]
  simp only [List.map_cons,List.map_nil]
  rw [show eval rho [(1993,1)]=rho 1993 by simp [eval],show eval rho [(8387,1)]=rho 8387 by simp [eval]]
theorem hash150 (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumeOutputHash918C150.result=((BalanceBlindingDomain670.crypto c).hash .noteNullifier [(w.auth.nk),(volumeState (BalanceBlindingDomain670.crypto c) w.volume.subject w.volume.dayStart w.volume.prior w.volume.priorBlinding),(w.volume.priorPosition)]:F) := by
  have zero : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 := by
    unfold assignment
    exact RoutingParameterValues879.zero _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial CapturedInitial73419Generic01.copy=1 := by
    unfold assignment
    exact RoutingParameterValues879.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic : SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
    unfold assignment
    exact RoutingParameterValues879.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have result := VolumeOutputHash918C150.hash _ zero (copied.trans zero.symm) arithmetic
  rw [ports150,VolumeOutputValues920.key original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumePriorValues909.hash_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumeOutputValues920.position original u c w legal rkInitial authInitial initial senderInitial receiverInitial] at result
  exact result.trans (natural150 c w).symm
theorem natural151 (c : Crypto) (w : TransferSem.Witness) :
    ((BalanceBlindingDomain670.crypto c).hash .volumeState [(w.volume.subject),(w.volume.dayStart),(w.volume.successor),(w.volume.successorBlinding)]:F)=Poseidon.hash6 (Poseidon.castParameters VolumeOutputHash918C151.parameters) 5 [(w.volume.subject:F),(w.volume.dayStart:F),(w.volume.successor:F),(w.volume.successorBlinding:F)] := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide ConcreteRegistrySharedEncoding294.representation
    .volumeState [(w.volume.subject),(w.volume.dayStart),(w.volume.successor),(w.volume.successorBlinding)]:F)=_
  rw [show Poseidon.castParameters VolumeOutputHash918C151.parameters=(RegistryNatural193.wide : Poseidon.Parameters F 6) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_neg (by change ¬4≤2;decide)]
  rfl
theorem ports151 (rho : Nat → F) : VolumeOutputHash918C151.inputs.map (eval rho)=[rho 7740,rho 7739,rho 7742,rho 8508] := by
  simp [VolumeOutputHash918C151.inputs,eval]
theorem hash151 (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumeOutputHash918C151.result=((BalanceBlindingDomain670.crypto c).hash .volumeState [(w.volume.subject),(w.volume.dayStart),(w.volume.successor),(w.volume.successorBlinding)]:F) := by
  have zero : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 := by
    unfold assignment
    exact RoutingParameterValues879.zero _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial CapturedInitial73419Generic01.copy=1 := by
    unfold assignment
    exact RoutingParameterValues879.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic : SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
    unfold assignment
    exact RoutingParameterValues879.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have result := VolumeOutputHash918C151.hash _ zero (copied.trans zero.symm) arithmetic
  rw [ports151,VolumeHashAssignment892.subject original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumePriorValues909.day_start original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumeOutputValues920.successor original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumeHashAssignment892.successorBlinding original u c w legal rkInitial authInitial initial senderInitial receiverInitial] at result
  exact result.trans (natural151 c w).symm
theorem natural152 (c : Crypto) (w : TransferSem.Witness) :
    ((BalanceBlindingDomain670.crypto c).hash .volumePaddingNullifier [(w.auth.nk),(w.nonce),(w.volume.dayStart)]:F)=Poseidon.hash6 (Poseidon.castParameters VolumeOutputHash918C152.parameters) 9 [(w.auth.nk:F),(w.nonce:F),(w.volume.dayStart:F)] := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide ConcreteRegistrySharedEncoding294.representation
    .volumePaddingNullifier [(w.auth.nk),(w.nonce),(w.volume.dayStart)]:F)=_
  rw [show Poseidon.castParameters VolumeOutputHash918C152.parameters=(RegistryNatural193.wide : Poseidon.Parameters F 6) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_neg (by change ¬3≤2;decide)]
  rfl
theorem ports152 (rho : Nat → F) : VolumeOutputHash918C152.inputs.map (eval rho)=[rho 1993,rho 8,rho 7739] := by
  simp [VolumeOutputHash918C152.inputs,eval]
theorem hash152 (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumeOutputHash918C152.result=((BalanceBlindingDomain670.crypto c).hash .volumePaddingNullifier [(w.auth.nk),(w.nonce),(w.volume.dayStart)]:F) := by
  have zero : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 := by
    unfold assignment
    exact RoutingParameterValues879.zero _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial CapturedInitial73419Generic01.copy=1 := by
    unfold assignment
    exact RoutingParameterValues879.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic : SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
    unfold assignment
    exact RoutingParameterValues879.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have result := VolumeOutputHash918C152.hash _ zero (copied.trans zero.symm) arithmetic
  rw [ports152,VolumeOutputValues920.key original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumeOutputValues920.nonce original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumePriorValues909.day_start original u c w legal rkInitial authInitial initial senderInitial receiverInitial] at result
  exact result.trans (natural152 c w).symm
theorem natural153 (c : Crypto) (w : TransferSem.Witness) :
    ((BalanceBlindingDomain670.crypto c).hash .volumePaddingCommitment [(w.auth.nk),(w.nonce),(w.volume.dayStart)]:F)=Poseidon.hash6 (Poseidon.castParameters VolumeOutputHash918C153.parameters) 8 [(w.auth.nk:F),(w.nonce:F),(w.volume.dayStart:F)] := by
  change (PoseidonNatural192.hash RegistryNatural193.small RegistryNatural193.wide ConcreteRegistrySharedEncoding294.representation
    .volumePaddingCommitment [(w.auth.nk),(w.nonce),(w.volume.dayStart)]:F)=_
  rw [show Poseidon.castParameters VolumeOutputHash918C153.parameters=(RegistryNatural193.wide : Poseidon.Parameters F 6) from rfl]
  rw [PoseidonNatural192.hash_cast]
  unfold Poseidon.hash
  rw [if_neg (by change ¬3≤2;decide)]
  rfl
theorem ports153 (rho : Nat → F) : VolumeOutputHash918C153.inputs.map (eval rho)=[rho 1993,rho 8,rho 7739] := by
  simp [VolumeOutputHash918C153.inputs,eval]
theorem hash153 (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    eval (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) VolumeOutputHash918C153.result=((BalanceBlindingDomain670.crypto c).hash .volumePaddingCommitment [(w.auth.nk),(w.nonce),(w.volume.dayStart)]:F) := by
  have zero : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial 0=1 := by
    unfold assignment
    exact RoutingParameterValues879.zero _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have copied : assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial CapturedInitial73419Generic01.copy=1 := by
    unfold assignment
    exact RoutingParameterValues879.copied _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic : SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) CapturedFullArithmetic52.rowAt 177954 := by
    unfold assignment
    exact RoutingParameterValues879.arithmetic _ u c w legal rkInitial authInitial initial senderInitial receiverInitial
  have result := VolumeOutputHash918C153.hash _ zero (copied.trans zero.symm) arithmetic
  rw [ports153,VolumeOutputValues920.key original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumeOutputValues920.nonce original u c w legal rkInitial authInitial initial senderInitial receiverInitial,VolumePriorValues909.day_start original u c w legal rkInitial authInitial initial senderInitial receiverInitial] at result
  exact result.trans (natural153 c w).symm
end ShielddSecurity.VolumeOutputMeaning921

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.natural149
#print axioms ShielddSecurity.VolumeOutputMeaning921.natural149

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.ports149
#print axioms ShielddSecurity.VolumeOutputMeaning921.ports149

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.hash149
#print axioms ShielddSecurity.VolumeOutputMeaning921.hash149

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.natural150
#print axioms ShielddSecurity.VolumeOutputMeaning921.natural150

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.ports150
#print axioms ShielddSecurity.VolumeOutputMeaning921.ports150

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.hash150
#print axioms ShielddSecurity.VolumeOutputMeaning921.hash150

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.natural151
#print axioms ShielddSecurity.VolumeOutputMeaning921.natural151

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.ports151
#print axioms ShielddSecurity.VolumeOutputMeaning921.ports151

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.hash151
#print axioms ShielddSecurity.VolumeOutputMeaning921.hash151

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.natural152
#print axioms ShielddSecurity.VolumeOutputMeaning921.natural152

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.ports152
#print axioms ShielddSecurity.VolumeOutputMeaning921.ports152

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.hash152
#print axioms ShielddSecurity.VolumeOutputMeaning921.hash152

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.natural153
#print axioms ShielddSecurity.VolumeOutputMeaning921.natural153

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.ports153
#print axioms ShielddSecurity.VolumeOutputMeaning921.ports153

set_option pp.all true in
#check @ShielddSecurity.VolumeOutputMeaning921.hash153
#print axioms ShielddSecurity.VolumeOutputMeaning921.hash153
