import ShielddSecurity.AuthorizationTraceBindings458
import ShielddSecurity.AuthorizationWindowRows455
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationWindows459
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51
open ConcretePointTorsion01 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem
open AuthorizationTraceAssignment457

theorem rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (ConcreteAuthorizationCrypto430.crypto c) w)
    (authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) (index window : Nat)
    (bound : index<2) (e : VariableWindowJoin443.Entry)
    (checked : AuthorizationWindowRows455.check ⟨AuthorizationWindowRows455.family index,window,e⟩=true) :
    VariableWindowJoin443.Rows (assignment original c w legal authInitial initial senderInitial receiverInitial) e := by
  have complete : AuthorizationWindowRows455.Complete ⟨AuthorizationWindowRows455.family index,window,e⟩ :=
    of_decide_eq_true checked
  have layout : VariableWindowLayout447.Valid (AuthorizationWindowRows455.family index) window e :=
    of_decide_eq_true complete.1
  have upper := layout.2.1
  apply AuthorizationWindowRows455.local_rows original
    (assignment original c w legal authInitial initial senderInitial receiverInitial)
    (bases c w legal) w.auth.ivk index window bound e checked
    (copied original c w legal authInitial initial senderInitial receiverInitial)
    (arithmetic original c w legal authInitial initial senderInitial receiverInitial)
    (AuthorizationTraceBindings458.base original c w legal authInitial initial senderInitial receiverInitial index bound)
    (hints original c w legal authInitial initial senderInitial receiverInitial)
  · have low := AuthorizationTraceBindings458.bits original c w legal authInitial initial senderInitial receiverInitial
      (250-2*window) (by omega)
    have indexEq : 2000+(250-2*window)=2250-2*window := by omega
    rw [indexEq] at low
    exact low
  · have high := AuthorizationTraceBindings458.bits original c w legal authInitial initial senderInitial receiverInitial
      (251-2*window) (by omega)
    have indexEq : 2000+(251-2*window)=2251-2*window := by omega
    rw [indexEq] at high
    exact high
end ShielddSecurity.AuthorizationWindows459
set_option pp.all true in
#check @ShielddSecurity.AuthorizationWindows459.rows
#print axioms ShielddSecurity.AuthorizationWindows459.rows
