import ShielddSecurity.MerkleSelection26Semantic
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
namespace ShielddSecurity.MerkleSelection26Controls
open Compiler CompilerCompletion CompilerIndexed01
open CapturedInitial73419Generic01 (p copy normalized)
open MerkleSelection26Data
def production (rows : Array Row) (mapping : Array Nat) (pivot : Linear) : Bool :=
  checkOriginalCoverage p copy rows (emitted steps).toArray mapping &&
  checkRow p (normalized rows.toList) ⟨left0++right0,[(25461,1)]++scaleLinear 4 pivot⟩
def indices : Array Nat := (List.range 13).toArray
theorem positive : production originalRows.toArray indices [(25460,1)]=true := by decide +kernel
theorem coefficient_rejected : production (originalRows.toArray.set! 0 ⟨(originalRows.toArray.getD 0 ⟨[],[]⟩).a++[(184,1)],(originalRows.toArray.getD 0 ⟨[],[]⟩).b⟩) indices [(25460,1)]=false := by decide +kernel
theorem existing_index_rejected : production originalRows.toArray (indices.set! 0 1) [(25460,1)]=false := by decide +kernel
theorem omission_rejected : production (originalRows.take 12).toArray indices [(25460,1)]=false := by decide +kernel
theorem pivot_rejected : production originalRows.toArray indices [(25462,1)]=false := by decide +kernel
theorem copy_link_rejected : production (originalRows.toArray.set! 12 ⟨[(0,1),(copy,-2)],[]⟩) indices [(25460,1)]=false := by decide +kernel
theorem every_position : originalRows.length=13 ∧ (emitted steps).length=13 ∧
    ∀ index : Fin 13, indices[index.val]?=some index.val ∧
      checkOriginalAt p copy originalRows.toArray (emitted steps).toArray indices index.val=true := by decide +kernel
end ShielddSecurity.MerkleSelection26Controls

set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Controls.production
#print axioms ShielddSecurity.MerkleSelection26Controls.production
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Controls.indices
#print axioms ShielddSecurity.MerkleSelection26Controls.indices
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Controls.positive
#print axioms ShielddSecurity.MerkleSelection26Controls.positive
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Controls.coefficient_rejected
#print axioms ShielddSecurity.MerkleSelection26Controls.coefficient_rejected
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Controls.existing_index_rejected
#print axioms ShielddSecurity.MerkleSelection26Controls.existing_index_rejected
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Controls.omission_rejected
#print axioms ShielddSecurity.MerkleSelection26Controls.omission_rejected
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Controls.pivot_rejected
#print axioms ShielddSecurity.MerkleSelection26Controls.pivot_rejected
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Controls.copy_link_rejected
#print axioms ShielddSecurity.MerkleSelection26Controls.copy_link_rejected
set_option pp.all true in
#check @ShielddSecurity.MerkleSelection26Controls.every_position
#print axioms ShielddSecurity.MerkleSelection26Controls.every_position
