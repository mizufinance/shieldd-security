import ShielddSecurity.CapturedMerkleWide223Pilot
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerklePaired225Pilot
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
noncomputable def front : List Row := (MerkleGlobalBody181.arithmeticRows 1).drop 320 |>.take 32
noncomputable def indices : List Nat := List.range' 3890 32
noncomputable def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices front
theorem checked : productionCheck=true := by decide +kernel
noncomputable def rows : List Row := (MerkleGlobalBody181.arithmeticRows 1).drop 320 |>.take 64
theorem partition : rows=front++CapturedMerkleWide223Pilot.rows := by
 change ((MerkleGlobalBody181.arithmeticRows 1).drop 320).take (32+32)=_
 rw [List.take_add,List.drop_drop]
 rfl
theorem count : rows.length=64 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho rows := by
 have first:=CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices front checked rho
   ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
 have second:=CapturedMerkleWide223Pilot.sound rho satisfied
 rw [partition]
 intro row member
 rcases List.mem_append.mp member with left|right
 · exact first row left
 · exact second row right
end ShielddSecurity.CapturedMerklePaired225Pilot

set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePaired225Pilot.front
#print axioms ShielddSecurity.CapturedMerklePaired225Pilot.front
set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePaired225Pilot.indices
#print axioms ShielddSecurity.CapturedMerklePaired225Pilot.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePaired225Pilot.productionCheck
#print axioms ShielddSecurity.CapturedMerklePaired225Pilot.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePaired225Pilot.checked
#print axioms ShielddSecurity.CapturedMerklePaired225Pilot.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePaired225Pilot.rows
#print axioms ShielddSecurity.CapturedMerklePaired225Pilot.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePaired225Pilot.partition
#print axioms ShielddSecurity.CapturedMerklePaired225Pilot.partition
set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePaired225Pilot.count
#print axioms ShielddSecurity.CapturedMerklePaired225Pilot.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerklePaired225Pilot.sound
#print axioms ShielddSecurity.CapturedMerklePaired225Pilot.sound
