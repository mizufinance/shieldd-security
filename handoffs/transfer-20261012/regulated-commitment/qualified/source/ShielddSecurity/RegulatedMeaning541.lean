import ShielddSecurity.RegulatedInputFrame536
import ShielddSecurity.RegulatedPointFrame537
import ShielddSecurity.RegulatedPorts539
import ShielddSecurity.RegulatedNatural540
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.RegulatedMeaning541
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
attribute [local irreducible] ConcreteRegistrySharedEncoding294.model SubgroupSeedCompletion203.fieldPoint
  PoseidonNatural192.hash Poseidon.hash6 Poseidon.hash3

def keyInputs (c : Crypto) (w : TransferSem.Witness) :=
  pointFields ((AuthorizationFixedDomain485.crypto c).mul w.auth.ivk w.sender.rnkDH) ++
    addressFields w.sender.address ++ [w.asset] ++ pointFields w.registry.ring

theorem inputs (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (data : RegulatedInputFrame536.Inputs rho w)
    (points : RegulatedPointFrame537.Points rho (AuthorizationFixedDomain485.withGenerator c) w)
    (one : rho 0=1) (copied : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (regulated : w.regulated=true) :
    AuthorizationHash530C56.values rho=(keyInputs c w).map (fun x => (x:F)) := by
  have flag : rho 10=1 := by simpa only [regulated,ite_true] using data.flag
  have dhx := congrArg Group.Point.x points.dh
  have dhy := congrArg Group.Point.y points.dh
  have div := points.sender 0
  have trans := points.sender 1
  change VariableWindowColumns449.columnPoint rho 1504=SubgroupSeedCompletion203.fieldPoint w.sender.address.diversified at div
  change VariableWindowColumns449.columnPoint rho 1512=SubgroupSeedCompletion203.fieldPoint w.sender.address.transmission at trans
  have ax := congrArg Group.Point.x div
  have ay := congrArg Group.Point.y div
  have tx := congrArg Group.Point.x trans
  have ty := congrArg Group.Point.y trans
  simp only [VariableWindowColumns449.columnPoint,SubgroupSeedCompletion203.fieldPoint,Nat.reduceAdd] at dhx dhy ax ay tx ty
  have ports := RegulatedPorts539.regulated_inputs rho one copied flag arithmetic _ _ _ _ _ _ _ _ _
    dhx dhy ax ay tx ty data.asset data.ringX data.ringY
  simpa only [keyInputs,pointFields,addressFields,List.map_append,List.map_cons,List.map_nil,
    List.cons_append,List.nil_append] using ports
set_option pp.all true in
#check @inputs
#print axioms inputs

theorem key_meaning (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (data : RegulatedInputFrame536.Inputs rho w)
    (points : RegulatedPointFrame537.Points rho (AuthorizationFixedDomain485.withGenerator c) w)
    (one : rho 0=1) (copied : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (regulated : w.regulated=true) :
    eval rho AuthorizationHash530C56.result=(rnk (AuthorizationFixedDomain485.crypto c) w:F) := by
  have hash := AuthorizationHash530C56.hash rho one (copied.trans one.symm) arithmetic
  rw [inputs rho c w data points one copied arithmetic regulated] at hash
  have natural := RegulatedNatural540.key_hash c (keyInputs c w) (by rfl)
  have selected : ring (AuthorizationFixedDomain485.crypto c) w=w.registry.ring := by
    simp only [ring,regulated,ite_true]
  have result := hash.trans natural.symm
  simpa only [rnk,selected,keyInputs] using result
set_option pp.all true in
#check @key_meaning
#print axioms key_meaning

theorem commitment_meaning (rho : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (data : RegulatedInputFrame536.Inputs rho w)
    (points : RegulatedPointFrame537.Points rho (AuthorizationFixedDomain485.withGenerator c) w)
    (one : rho 0=1) (copied : rho copy=1)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954)
    (regulated : w.regulated=true) :
    eval rho AuthorizationHash530C57.result=
      ((AuthorizationFixedDomain485.crypto c).hash .regulatedNullifierCommitment [rnk (AuthorizationFixedDomain485.crypto c) w]:F) := by
  have key := key_meaning rho c w data points one copied arithmetic regulated
  have hash := AuthorizationHash530C57.hash rho one (copied.trans one.symm) arithmetic
  have ports : AuthorizationHash530C57.values rho=[eval rho AuthorizationHash530C56.result] := rfl
  rw [ports,key] at hash
  exact hash.trans (RegulatedNatural540.commitment_hash c _).symm
set_option pp.all true in
#check @commitment_meaning
#print axioms commitment_meaning
end ShielddSecurity.RegulatedMeaning541
