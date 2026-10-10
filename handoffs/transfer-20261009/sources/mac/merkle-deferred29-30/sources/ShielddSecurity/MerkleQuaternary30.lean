import ShielddSecurity.MerkleBits29
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.MerkleQuaternary30
open Compiler Poseidon CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
variable {F : Type} [Field F]
def boolValue (bit : Bool) : F := if bit then 1 else 0
def children (low high : Bool) (node sibling0 sibling1 sibling2 : F) (i : Fin 4) : F :=
  if high then
    if low then ([sibling0,sibling1,sibling2,node] : List F).getD i.val 0
    else ([sibling0,sibling1,node,sibling2] : List F).getD i.val 0
  else
    if low then ([sibling0,node,sibling1,sibling2] : List F).getD i.val 0
    else ([node,sibling0,sibling1,sibling2] : List F).getD i.val 0
theorem formula_boolean (low high : Bool) (node s0 s1 s2 : F) :
    MerkleSelection26Semantic.formula (boolValue low) (boolValue high) node s0 s1 s2=children low high node s0 s1 s2 := by
  cases low <;> cases high <;> funext i
  all_goals
    have cases : i=⟨0,by decide⟩ ∨ i=⟨1,by decide⟩ ∨ i=⟨2,by decide⟩ ∨ i=⟨3,by decide⟩ := by have h:=i.isLt;simp only [Fin.ext_iff];omega
    rcases cases with rfl|rfl|rfl|rfl <;> simp [MerkleSelection26Semantic.formula,boolValue,children]
theorem encoded (x : F) (bit : x=0 ∨ x=1) : ∃ b : Bool,x=boolValue b := by
  rcases bit with zero|one
  · exact ⟨false,zero⟩
  · exact ⟨true,one⟩
variable [CharP F p]
theorem arbitrary (rho : Nat → F) (one : rho 0=1)
    (prior : Satisfies rho MerkleHash27Whole.priorRows) (hashRows : Satisfies rho MerkleHash27Whole.selectedRows)
    (bits : Satisfies rho MerkleBits29.actualRows) :
    ∃ low high : Bool,rho 184=boolValue low ∧ rho 185=boolValue high ∧
      eval rho MerkleHash27Whole.actualResult=Poseidon.hash6 (castParameters MerkleHash27R0Data.parameters) 2
        [1,children low high (MerkleInputMeaning28.registryMeaning rho) (rho 136) (rho 137) (rho 138) 0,
         children low high (MerkleInputMeaning28.registryMeaning rho) (rho 136) (rho 137) (rho 138) 1,
         children low high (MerkleInputMeaning28.registryMeaning rho) (rho 136) (rho 137) (rho 138) 2,
         children low high (MerkleInputMeaning28.registryMeaning rho) (rho 136) (rho 137) (rho 138) 3] := by
  have lowBit : rho 184=0 ∨ rho 184=1 := by simpa using MerkleBits29.bits_sound rho bits (⟨0,by decide⟩ : Fin 32)
  have highBit : rho 185=0 ∨ rho 185=1 := by simpa using MerkleBits29.bits_sound rho bits (⟨1,by decide⟩ : Fin 32)
  obtain ⟨low,lowEq⟩ := encoded _ lowBit
  obtain ⟨high,highEq⟩ := encoded _ highBit
  have result := MerkleInputMeaning28.arbitrary rho one prior hashRows
  unfold MerkleInputMeaning28.pathMeaning at result
  rw [lowEq,highEq,formula_boolean] at result
  exact ⟨low,high,lowEq,highEq,result⟩
def production (rows : Array Row) (mapping : Array Nat) : Bool :=
  checkOriginalCoverage p 0 rows MerkleBits29.referenceRows.toArray mapping &&
  checkOriginalCoverage p 0 MerkleBits29.referenceRows.toArray rows mapping
theorem positive : production MerkleBits29.actualRows.toArray MerkleBits29.mapping=true :=
  Bool.and_eq_true_iff.mpr ⟨MerkleBits29.actual_to_reference_checked,MerkleBits29.reference_to_actual_checked⟩
theorem coefficient_rejected : production (MerkleBits29.actualRows.toArray.set! 0 ⟨[(184,2)],[(184,1)]⟩) MerkleBits29.mapping=false := by decide +kernel
theorem existing_index_rejected : production MerkleBits29.actualRows.toArray (MerkleBits29.mapping.set! 0 1)=false := by decide +kernel
theorem omission_rejected : production (MerkleBits29.actualRows.take 33).toArray MerkleBits29.mapping=false := by decide +kernel
theorem position_rejected : production (MerkleBits29.actualRows.toArray.set! 32 ⟨[(136,-1)]++weighted MerkleBits29.columns 1,[]⟩) MerkleBits29.mapping=false := by decide +kernel
theorem every_position : ∀ index : Fin 34,
    checkOriginalAt p 0 MerkleBits29.actualRows.toArray MerkleBits29.referenceRows.toArray MerkleBits29.mapping index.val=true := by decide +kernel
end ShielddSecurity.MerkleQuaternary30

set_option pp.all true in
#check @ShielddSecurity.MerkleQuaternary30.boolValue
#print axioms ShielddSecurity.MerkleQuaternary30.boolValue
set_option pp.all true in
#check @ShielddSecurity.MerkleQuaternary30.children
#print axioms ShielddSecurity.MerkleQuaternary30.children
set_option pp.all true in
#check @ShielddSecurity.MerkleQuaternary30.formula_boolean
#print axioms ShielddSecurity.MerkleQuaternary30.formula_boolean
set_option pp.all true in
#check @ShielddSecurity.MerkleQuaternary30.encoded
#print axioms ShielddSecurity.MerkleQuaternary30.encoded
set_option pp.all true in
#check @ShielddSecurity.MerkleQuaternary30.arbitrary
#print axioms ShielddSecurity.MerkleQuaternary30.arbitrary
set_option pp.all true in
#check @ShielddSecurity.MerkleQuaternary30.production
#print axioms ShielddSecurity.MerkleQuaternary30.production
set_option pp.all true in
#check @ShielddSecurity.MerkleQuaternary30.positive
#print axioms ShielddSecurity.MerkleQuaternary30.positive
set_option pp.all true in
#check @ShielddSecurity.MerkleQuaternary30.coefficient_rejected
#print axioms ShielddSecurity.MerkleQuaternary30.coefficient_rejected
set_option pp.all true in
#check @ShielddSecurity.MerkleQuaternary30.existing_index_rejected
#print axioms ShielddSecurity.MerkleQuaternary30.existing_index_rejected
set_option pp.all true in
#check @ShielddSecurity.MerkleQuaternary30.omission_rejected
#print axioms ShielddSecurity.MerkleQuaternary30.omission_rejected
set_option pp.all true in
#check @ShielddSecurity.MerkleQuaternary30.position_rejected
#print axioms ShielddSecurity.MerkleQuaternary30.position_rejected
set_option pp.all true in
#check @ShielddSecurity.MerkleQuaternary30.every_position
#print axioms ShielddSecurity.MerkleQuaternary30.every_position
