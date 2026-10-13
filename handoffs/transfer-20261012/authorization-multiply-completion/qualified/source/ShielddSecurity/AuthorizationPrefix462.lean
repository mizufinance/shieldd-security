import ShielddSecurity.AuthorizationTraceBindings458
import ShielddSecurity.VariableTraceAccess452
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationPrefix462
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationTraceAssignment457 AuthorizationTraceSeed451 AuthorizationTraceIndex450

theorem first_output (base : curve.Point) (scalar : Nat) :
    (windowAt base scalar 0).output=
      Group.windowPoint (if (windowAt base scalar 0).low then 1 else 0)
        (if (windowAt base scalar 0).high then 1 else 0)
        (model.coordinates base) (model.coordinates (2 • base)) (model.coordinates (3 • base)) := by
  have length : ((VariableTraceBits446.pairs (encodeBits 252 scalar)).reverse).length=126 := by
    simp [VariableTraceBits446.pairs_length]
  cases parts : (VariableTraceBits446.pairs (encodeBits 252 scalar)).reverse with
  | nil => simp [parts] at length
  | cons head tail =>
    have result := VariableTraceAccess452.first_selection model base head tail empty
    unfold windowAt trace VariableTraceBits446.windows
    rw [parts]
    simpa only [VariableTraceConstruction442.trace,List.getElem?_cons_zero,Option.getD_some,
      VariableTraceConstruction442.window] using result.symm

theorem prefix_point (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index point : Nat)
    (bound : index<2) (pointBound : point<3) :
    VariableWindowColumns449.columnPoint
      (assignment original c w legal authInitial initial senderInitial receiverInitial) (column index 0 point 0)=
    hintPoint (bases c w legal index) w.auth.ivk point := by
  have preserved := completed_point (seed original (bases c w legal) w.auth.ivk)
    (ConcreteAuthorizationCrypto430.withOperations c) w authInitial initial senderInitial receiverInitial
    (column index 0 point 0) (by unfold column;omega) (by unfold column;omega)
  exact preserved.trans (AuthorizationTraceSeed451.prefix_point original (bases c w legal) w.auth.ivk index point bound pointBound)

theorem precompute_equations (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index : Nat) (bound : index<2) :
    let rho := assignment original c w legal authInitial initial senderInitial receiverInitial
    TransferOwnership.DoubleEquations (VariableWindowColumns449.columnPoint rho (1504+16*index))
      (VariableWindowColumns449.columnPoint rho (2253+756*index)) ∧
    TransferOwnership.AddEquations (CapturedFirstSubgroup81.d:F)
      (VariableWindowColumns449.columnPoint rho (1504+16*index))
      (VariableWindowColumns449.columnPoint rho (2253+756*index))
      (VariableWindowColumns449.columnPoint rho (2255+756*index)) := by
  dsimp only
  have twice := prefix_point original c w legal authInitial initial senderInitial receiverInitial index 0 bound (by decide)
  have triple := prefix_point original c w legal authInitial initial senderInitial receiverInitial index 1 bound (by decide)
  change VariableWindowColumns449.columnPoint _ (2253+756*index)=model.coordinates (2 • bases c w legal index) at twice
  have pos : column index 0 1 0=2255+756*index := by unfold column;omega
  rw [pos] at triple
  change VariableWindowColumns449.columnPoint _ (2255+756*index)=model.coordinates (3 • bases c w legal index) at triple
  rw [AuthorizationTraceBindings458.base original c w legal authInitial initial senderInitial receiverInitial index bound,twice,triple]
  have nonSquare := (show Group.NoUnitSquare (CapturedFirstSubgroup81.d:F) from by
    rw [coefficient_eq];exact ConcreteJubjubField01.coefficient_no_unit_square)
  constructor
  · exact VariableGroupCompletion439.double_equations (CapturedFirstSubgroup81.d:F) imaginary model nonSquare imaginary_square _
  · have three : bases c w legal index+2 • bases c w legal index=3 • bases c w legal index := by
      rw [show 3=2+1 from rfl,add_nsmul,one_nsmul,add_comm]
    rw [←three]
    exact VariableGroupCompletion439.add_equations (CapturedFirstSubgroup81.d:F) imaginary model nonSquare imaginary_square _ _
end ShielddSecurity.AuthorizationPrefix462

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPrefix462.first_output
#print axioms ShielddSecurity.AuthorizationPrefix462.first_output

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPrefix462.prefix_point
#print axioms ShielddSecurity.AuthorizationPrefix462.prefix_point

set_option pp.all true in
#check @ShielddSecurity.AuthorizationPrefix462.precompute_equations
#print axioms ShielddSecurity.AuthorizationPrefix462.precompute_equations
