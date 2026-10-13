import ShielddSecurity.ScalarCanonicalConstruction397
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.AuthorizationClamp398
open ConcreteJubjubField01 ConcreteRegistrySharedEncoding294 TransferSem

def maximum : Nat := TransferCore.fieldModulus-1-8*TransferCore.scalarOrder

theorem hash_bound (c : Crypto) (domain : Domain) (inputs : List Nat) :
    (crypto c).hash domain inputs<TransferCore.fieldModulus :=
  PoseidonNatural192.hash_bound RegistryNatural193.small RegistryNatural193.wide representation domain inputs

theorem reduction_bound (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) :
    w.auth.ivk+TransferCore.scalarOrder*w.auth.quotient<TransferCore.fieldModulus := by
  have scalar := legal.2.1.2.2.2.1.2.2.2.2.1
  rw [←scalar.2.2.2]
  exact hash_bound c .incomingViewingKey ([w.auth.nk]++pointFields w.auth.ak)

theorem quotient_eight_bound (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (crypto c) w) (eight : w.auth.quotient=8) :
    w.auth.ivk≤maximum := by
  have bound := reduction_bound c w legal
  rw [eight] at bound
  unfold maximum
  have size : 8*TransferCore.scalarOrder<TransferCore.fieldModulus := by decide +kernel
  have commuted : TransferCore.scalarOrder*8=8*TransferCore.scalarOrder := Nat.mul_comm _ _
  rw [commuted] at bound
  omega

theorem maximum_below_scalar : maximum<TransferCore.scalarOrder := by decide +kernel

end ShielddSecurity.AuthorizationClamp398

set_option pp.all true in
#check @ShielddSecurity.AuthorizationClamp398.maximum
#print axioms ShielddSecurity.AuthorizationClamp398.maximum

set_option pp.all true in
#check @ShielddSecurity.AuthorizationClamp398.hash_bound
#print axioms ShielddSecurity.AuthorizationClamp398.hash_bound

set_option pp.all true in
#check @ShielddSecurity.AuthorizationClamp398.reduction_bound
#print axioms ShielddSecurity.AuthorizationClamp398.reduction_bound

set_option pp.all true in
#check @ShielddSecurity.AuthorizationClamp398.quotient_eight_bound
#print axioms ShielddSecurity.AuthorizationClamp398.quotient_eight_bound

set_option pp.all true in
#check @ShielddSecurity.AuthorizationClamp398.maximum_below_scalar
#print axioms ShielddSecurity.AuthorizationClamp398.maximum_below_scalar
