import ShielddSecurity.AuthorizationInitial466
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationFinalPoint467
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationTraceAssignment457 AuthorizationTraceSeed451 AuthorizationTraceIndex450

theorem before_length {K : Type} [Field K] (input : Group.Point K) (windows : List (TransferOwnership.WindowWitness K))
    (fallback : TransferOwnership.WindowWitness K) :
    VariableTraceAccess452.before input windows fallback windows.length=TransferOwnership.traceOutput input windows := by
  induction windows generalizing input with
  | nil => rfl
  | cons head tail ih =>
    rw [List.length_cons,VariableTraceAccess452.before_cons]
    exact ih head.output

theorem last_output (base : curve.Point) (scalar : Nat) (bound : scalar<2^252) :
    (windowAt base scalar 125).output=model.coordinates (scalar • base) := by
  have last := before_length (model.coordinates 0) (trace base scalar) empty
  rw [AuthorizationTraceLocal453.trace_length] at last
  change (windowAt base scalar 125).output=TransferOwnership.traceOutput (model.coordinates 0) (trace base scalar) at last
  rw [last]
  exact VariableTraceBits446.encoded_output (CapturedFirstSubgroup81.d:F) imaginary model
    (by rw [coefficient_eq];exact ConcreteJubjubField01.coefficient_no_unit_square)
    imaginary_square base 252 scalar bound

theorem final_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (bound : index<2) :
    VariableWindowColumns449.columnPoint
      (assignment original c w legal authInitial initial senderInitial receiverInitial) (3007+756*index)=
    model.coordinates (w.auth.ivk • bases c w legal index) := by
  have preserved := completed_point (seed original (bases c w legal) w.auth.ivk)
    (ConcreteAuthorizationCrypto430.withOperations c) w authInitial initial senderInitial receiverInitial
    (3007+756*index) (by omega) (by omega)
  have stored := window_point original (bases c w legal) w.auth.ivk index 125 2 bound (by decide) (by decide) (by decide)
  have pos : column index 125 2 0=3007+756*index := by unfold column;omega
  rw [pos] at stored
  change VariableWindowColumns449.columnPoint _ (3007+756*index)=(windowAt (bases c w legal index) w.auth.ivk 125).output at stored
  exact preserved.trans (stored.trans (last_output (bases c w legal index) w.auth.ivk
    (AuthScalarSeed366.legal_bounds (ConcreteAuthorizationCrypto430.withOperations c) w legal).2.1))

theorem transmission (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    VariableWindowColumns449.columnPoint
      (assignment original c w legal authInitial initial senderInitial receiverInitial) 3007=
    VariableWindowColumns449.columnPoint
      (assignment original c w legal authInitial initial senderInitial receiverInitial) 1512 := by
  have final := final_point original c w legal authInitial initial senderInitial receiverInitial 0 (by decide)
  change VariableWindowColumns449.columnPoint _ 3007=
    model.coordinates (w.auth.ivk • AuthorizationGroupDomain445.represented c w legal ⟨0,by decide⟩) at final
  rw [AuthorizationGroupDomain445.transmission] at final
  have sender := AuthorizationTraceBindings458.sender_point original c w legal authInitial initial senderInitial receiverInitial ⟨1,by decide⟩
  exact final.trans sender.symm
end ShielddSecurity.AuthorizationFinalPoint467

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFinalPoint467.before_length
#print axioms ShielddSecurity.AuthorizationFinalPoint467.before_length

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFinalPoint467.last_output
#print axioms ShielddSecurity.AuthorizationFinalPoint467.last_output

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFinalPoint467.final_point
#print axioms ShielddSecurity.AuthorizationFinalPoint467.final_point

set_option pp.all true in
#check @ShielddSecurity.AuthorizationFinalPoint467.transmission
#print axioms ShielddSecurity.AuthorizationFinalPoint467.transmission
