import ShielddSecurity.MapRootBits725
import ShielddSecurity.MapInverseRows722
import ShielddSecurity.MapRootCanonicalRows728F00
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MapRootCanonicalJoin730
open ConcreteJubjubField01 TransferSem
open MapAssignmentValues720 (assignment)
attribute [local irreducible] assignment ConcreteRegistrySharedEncoding294.model CompilerAssertionBlock51.SatisfiesAt

theorem rows (original : Nat → F) (u : F) (c : Crypto) (w : TransferSem.Witness)
    (legal : TransferSem.TransferSem (BalanceBlindingDomain670.crypto c) w)
    (rkInitial authInitial : Group.Point F) (initial : Fin 4 → Group.Point F)
    (senderInitial receiverInitial : Fin 3 → Group.Point F) :
    CompilerAssertionBlock51.SatisfiesAt (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
      (fun i => CapturedFullRelation58.rowAt (177954+21255+i)) 2 := by
  apply MapRootCanonicalRows728F00.complete
    (assignment original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (BalanceMapRoots700.selectedRoot u).val (MapRootBits725.root_bound u)
    (MapInverseRows722.zero original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (MapAssignmentValues720.copied original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
    (MapAssignmentValues720.arithmetic original u c w legal rkInitial authInitial initial senderInitial receiverInitial)
  intro index before
  exact MapRootBits725.bits original u c w legal rkInitial authInitial initial senderInitial receiverInitial index before
end ShielddSecurity.MapRootCanonicalJoin730

set_option pp.all true in
#check @ShielddSecurity.MapRootCanonicalJoin730.rows
#print axioms ShielddSecurity.MapRootCanonicalJoin730.rows
