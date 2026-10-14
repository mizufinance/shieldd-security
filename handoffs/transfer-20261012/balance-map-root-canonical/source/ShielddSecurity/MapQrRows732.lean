import ShielddSecurity.MapRootRows708
import ShielddSecurity.MapAssignmentValues720
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapQrRows732
open Compiler CompilerArithmeticTransport41 CompilerAssertionBlock51 ConcreteJubjubField01 TransferSem
open BalanceMapParameters699 MapAssignmentValues720
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model SatisfiesAt

noncomputable def assertionRows : List Row := [⟨[(20936,1)],[(189649,5),(189653,1)]⟩]
theorem captured : CompilerRowSlice63.check CapturedFullRelation58.rowAt (177954+20997) 1 assertionRows=true := by decide +kernel

theorem rows (rho : Nat → F) (u : F)
    (one : rho copy=1) (inverse : rho 20934=(sourceDenominator u)⁻¹)
    (flag : rho 20935=if BalanceMapRoots700.choice u then 1 else 0)
    (qr : rho 20936=BalanceMapRoots700.qrRoot u)
    (arithmetic : SatisfiesAt rho CapturedFullArithmetic52.rowAt 177954) :
    SatisfiesAt rho (fun i => CapturedFullRelation58.rowAt (177954+20997+i)) 1 := by
  have cubic := MapFirstCubic707.first_cubic rho u one inverse arithmetic
  have target := MapRootRows708.qr_target rho u flag cubic arithmetic
  apply (CompilerRowSlice63.selected_satisfies_iff CapturedFullRelation58.rowAt (177954+20997) 1 assertionRows captured rho).mp
  intro row member
  simp only [assertionRows,List.mem_cons,List.not_mem_nil,or_false] at member
  subst row
  simp only [eval,Int.cast_one,one_mul,add_zero,Int.cast_ofNat]
  change rho 20936*rho 20936=5*rho 189649+rho 189653
  rw [qr,target]
  simpa only [pow_two] using BalanceMapRoots700.qr_square u

theorem completed_rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+20997+i)) 1 := by
  have value := MapAssignmentValues720.values original u c w legal rkInitial authInitial initial senderInitial receiverInitial
  exact rows (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial) u
    value.copied value.initialInverse value.flag
    ((stable_value original u c w legal rkInitial authInitial initial senderInitial receiverInitial 20936
      (by change 20936∈MapWitnessLayout715.values;decide)).trans (MapSeedValues724.qr u))
    (MapAssignmentValues720.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
end ShielddSecurity.MapQrRows732

set_option pp.all true in
#check @ShielddSecurity.MapQrRows732.captured
#print axioms ShielddSecurity.MapQrRows732.captured

set_option pp.all true in
#check @ShielddSecurity.MapQrRows732.rows
#print axioms ShielddSecurity.MapQrRows732.rows

set_option pp.all true in
#check @ShielddSecurity.MapQrRows732.completed_rows
#print axioms ShielddSecurity.MapQrRows732.completed_rows
