import ShielddSecurity.MerkleGlobalBody181
import ShielddSecurity.CapturedArithmetic45B0018
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedMerkleLocal229Pilot
open Compiler CompilerAssertionBlock51
open CapturedInitial73419Generic01 (p copy)
def rows : List Row := ((TransferPoseidonTailTemplate05Program01.originalRows.drop 268).take 16).map
 (fun row => CompilerColumnRenaming05.row (CompilerWindowRenaming05.swap 25064 396 (MerkleFamily32Tables.offset 1))
   (CompilerColumnRenaming05.row R22.ren row))
theorem rows_exact : rows=(MerkleGlobalBody181.arithmeticRows 1).drop 320 |>.take 16 := by rfl
def indices : List Nat := List.range' 3890 16
def localParent (position : Nat) : Option Row := CapturedArithmetic45B0018.actual[position-3862]?
def localCheck : Bool := CompilerIndexedCopyStream171.check p copy localParent 200770 indices rows
theorem local_checked : localCheck=true := by decide +kernel
theorem parent_equal (position : Nat) (member : position ∈ indices) :
 CapturedFullRelation58.rowAt position=localParent position := by
 change position ∈ [3890,3891,3892,3893,3894,3895,3896,3897,3898,3899,3900,3901,3902,3903,3904,3905] at member
 simp only [List.mem_cons,List.mem_singleton] at member
 rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals rfl
theorem check_congr (parent localParent : Nat → Option Row) (indices : List Nat) (targets : List Row)
 (equal : ∀ position ∈ indices,parent position=localParent position) :
 CompilerIndexedCopyStream171.check p copy parent 200770 indices targets=
 CompilerIndexedCopyStream171.check p copy localParent 200770 indices targets := by
 induction indices generalizing targets with
 | nil => rfl
 | cons position rest ih =>
   cases targets with
   | nil => rfl
   | cons target targets =>
     simp only [CompilerIndexedCopyStream171.check,CompilerIndexedCopyStream171.rowCheck]
     rw [equal position (List.mem_cons_self _ _)]
     rw [ih targets (fun i h => equal i (List.mem_cons_of_mem _ h))]
def productionCheck : Bool := CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows
theorem checked : productionCheck=true := by
 change CompilerIndexedCopyStream171.check p copy CapturedFullRelation58.rowAt 200770 indices rows=true
 rw [check_congr CapturedFullRelation58.rowAt localParent indices rows parent_equal]
 exact local_checked
theorem count : rows.length=16 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
theorem sound (rho : Nat → F) (satisfied : SatisfiesAt rho CapturedFullRelation58.rowAt 200770) :
 Satisfies rho ((MerkleGlobalBody181.arithmeticRows 1).drop 320 |>.take 16) := by
 rw [←rows_exact]
 exact CompilerIndexedCopyStream171.sound copy CapturedFullRelation58.rowAt 200770 indices rows checked rho
  ((CapturedFullRelation58.verifier_links rho satisfied).2.2) satisfied
end ShielddSecurity.CapturedMerkleLocal229Pilot

set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal229Pilot.rows
#print axioms ShielddSecurity.CapturedMerkleLocal229Pilot.rows
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal229Pilot.rows_exact
#print axioms ShielddSecurity.CapturedMerkleLocal229Pilot.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal229Pilot.indices
#print axioms ShielddSecurity.CapturedMerkleLocal229Pilot.indices
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal229Pilot.localParent
#print axioms ShielddSecurity.CapturedMerkleLocal229Pilot.localParent
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal229Pilot.localCheck
#print axioms ShielddSecurity.CapturedMerkleLocal229Pilot.localCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal229Pilot.local_checked
#print axioms ShielddSecurity.CapturedMerkleLocal229Pilot.local_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal229Pilot.parent_equal
#print axioms ShielddSecurity.CapturedMerkleLocal229Pilot.parent_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal229Pilot.check_congr
#print axioms ShielddSecurity.CapturedMerkleLocal229Pilot.check_congr
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal229Pilot.productionCheck
#print axioms ShielddSecurity.CapturedMerkleLocal229Pilot.productionCheck
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal229Pilot.checked
#print axioms ShielddSecurity.CapturedMerkleLocal229Pilot.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal229Pilot.count
#print axioms ShielddSecurity.CapturedMerkleLocal229Pilot.count
set_option pp.all true in
#check @ShielddSecurity.CapturedMerkleLocal229Pilot.sound
#print axioms ShielddSecurity.CapturedMerkleLocal229Pilot.sound
