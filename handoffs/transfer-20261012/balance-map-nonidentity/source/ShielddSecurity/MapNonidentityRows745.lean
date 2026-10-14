import ShielddSecurity.MapAssetDomain743
import ShielddSecurity.MapNonidentityCapture744
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapNonidentityRows745
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open MapAssignmentValues720 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model ConcreteCofactorModel01.model SatisfiesAt

theorem rows (original : Nat → F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (MapAssetDomain743.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original (MapAssetHashMeaning740.input (MapAssetDomain743.withAsset c) w)
      (MapAssetDomain743.withAsset c) w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+21265+i)) 1 := by
  let chosen := MapAssetDomain743.withAsset c
  let u := MapAssetHashMeaning740.input chosen w
  have values := MapAssignmentValues720.values original u chosen w legal rkInitial authInitial initial senderInitial receiverInitial
  have arithmetic := MapAssignmentValues720.arithmetic original u chosen w legal rkInitial authInitial initial senderInitial receiverInitial
  have coordinates := (MapCofactorJoin714.doublings _ u values arithmetic).2.2.2
  have x := congrArg Group.Point.x coordinates
  change assignment original u chosen w legal rkInitial authInitial initial senderInitial receiverInitial 190237=(BalanceMapPoint701.eight u).x at x
  have last := (MapAssignmentValues720.stable_value original u chosen w legal rkInitial authInitial initial senderInitial receiverInitial 21198
    (by change 21198∈MapWitnessLayout715.values;decide)).trans (MapSeedValues724.last u)
  have product := MapNonidentityCapture744.equation _ arithmetic
  rw [last,x] at product
  have inverse := product.trans (inv_mul_cancel₀ (MapAssetDomain743.x_nonzero c w legal))
  exact MapNonidentityCapture744.rows _ values.copied inverse
end ShielddSecurity.MapNonidentityRows745

set_option pp.all true in
#check @ShielddSecurity.MapNonidentityRows745.rows
#print axioms ShielddSecurity.MapNonidentityRows745.rows
