import ShielddSecurity.SharedUserSubgroups356
import ShielddSecurity.CapturedUserNonidentity358
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.SharedUserNonidentity359
open Compiler CompilerArithmeticTransport41 ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

theorem outputs_one (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (registryInitial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    ∀ index<6, UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w registryInitial
      (CapturedUserNonidentity358.output index)=1 := by
  let base := UserSubgroupSeed352.seed original w senderInitial receiverInitial
  let rho := UserLifecycleWord345.assignment base c w registryInitial
  intro index bound
  have product := CapturedUserNonidentity358.products rho
    (SharedHighZeroRows333.arithmetic (UserWordSeed342.seed base w) c w registryInitial) index bound
  have cases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl|rfl
  · have first := UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨0,by decide⟩
    have inverse := UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨7,by decide⟩
    change rho 1504=((UserPointDomain351.point w.sender ⟨0,by decide⟩).x:F) at first
    change rho 1511=((UserPointDomain351.point w.sender ⟨0,by decide⟩).x:F)⁻¹ at inverse
    change rho 33872=rho 1504*rho 1511 at product
    rw [first,inverse] at product
    exact product.trans (UserPointDomain351.inverse_equation c w w.sender legal.2.1.2.1 ⟨0,by decide⟩)
  · have first := UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨0,by decide⟩
    have inverse := UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨7,by decide⟩
    change rho 1512=((UserPointDomain351.point w.sender ⟨1,by decide⟩).x:F) at first
    change rho 1519=((UserPointDomain351.point w.sender ⟨1,by decide⟩).x:F)⁻¹ at inverse
    change rho 33938=rho 1512*rho 1519 at product
    rw [first,inverse] at product
    exact product.trans (UserPointDomain351.inverse_equation c w w.sender legal.2.1.2.1 ⟨1,by decide⟩)
  · have first := UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨0,by decide⟩
    have inverse := UserSubgroupFrame354.sender_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨7,by decide⟩
    change rho 1520=((UserPointDomain351.point w.sender ⟨2,by decide⟩).x:F) at first
    change rho 1527=((UserPointDomain351.point w.sender ⟨2,by decide⟩).x:F)⁻¹ at inverse
    change rho 34004=rho 1520*rho 1527 at product
    rw [first,inverse] at product
    exact product.trans (UserPointDomain351.inverse_equation c w w.sender legal.2.1.2.1 ⟨2,by decide⟩)
  · have first := UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨0,by decide⟩
    have inverse := UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨0,by decide⟩ ⟨7,by decide⟩
    change rho 1742=((UserPointDomain351.point w.receiver ⟨0,by decide⟩).x:F) at first
    change rho 1749=((UserPointDomain351.point w.receiver ⟨0,by decide⟩).x:F)⁻¹ at inverse
    change rho 41826=rho 1742*rho 1749 at product
    rw [first,inverse] at product
    exact product.trans (UserPointDomain351.inverse_equation c w w.receiver legal.2.1.2.2.1 ⟨0,by decide⟩)
  · have first := UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨0,by decide⟩
    have inverse := UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨1,by decide⟩ ⟨7,by decide⟩
    change rho 1750=((UserPointDomain351.point w.receiver ⟨1,by decide⟩).x:F) at first
    change rho 1757=((UserPointDomain351.point w.receiver ⟨1,by decide⟩).x:F)⁻¹ at inverse
    change rho 41892=rho 1750*rho 1757 at product
    rw [first,inverse] at product
    exact product.trans (UserPointDomain351.inverse_equation c w w.receiver legal.2.1.2.2.1 ⟨1,by decide⟩)
  · have first := UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨0,by decide⟩
    have inverse := UserSubgroupFrame354.receiver_value original c w registryInitial senderInitial receiverInitial ⟨2,by decide⟩ ⟨7,by decide⟩
    change rho 1758=((UserPointDomain351.point w.receiver ⟨2,by decide⟩).x:F) at first
    change rho 1765=((UserPointDomain351.point w.receiver ⟨2,by decide⟩).x:F)⁻¹ at inverse
    change rho 41958=rho 1758*rho 1765 at product
    rw [first,inverse] at product
    exact product.trans (UserPointDomain351.inverse_equation c w w.receiver legal.2.1.2.2.1 ⟨2,by decide⟩)

theorem all_rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (registryInitial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CapturedUserNonidentity358.Rows
      (UserLifecycleWord345.assignment (UserSubgroupSeed352.seed original w senderInitial receiverInitial) c w registryInitial) := by
  let base := UserSubgroupSeed352.seed original w senderInitial receiverInitial
  let rho := UserLifecycleWord345.assignment base c w registryInitial
  have zero := SharedHighZeroRows333.zero (UserWordSeed342.seed base w) c w registryInitial
  have linked := SharedComparisonBlocks327.linked (HighZeroSeed329.seed (UserWordSeed342.seed base w) w) c w registryInitial
  change rho 0=1 at zero
  change rho copy=rho 0 at linked
  exact CapturedUserNonidentity358.complete rho zero linked (outputs_one original c w legal registryInitial senderInitial receiverInitial)
end ShielddSecurity.SharedUserNonidentity359

set_option pp.all true in
#check @ShielddSecurity.SharedUserNonidentity359.outputs_one
#print axioms ShielddSecurity.SharedUserNonidentity359.outputs_one

set_option pp.all true in
#check @ShielddSecurity.SharedUserNonidentity359.all_rows
#print axioms ShielddSecurity.SharedUserNonidentity359.all_rows
